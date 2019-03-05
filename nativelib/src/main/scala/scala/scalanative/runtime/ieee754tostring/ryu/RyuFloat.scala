// Copyright 2018 Ulf Adams
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Credits:
//
//    1) This work is a heavily modified derivation of the original work by
//       Ulf Adams at URL: https://github.com/ulfjack/ryu.
//       As such, it inherits the Apache license of the original work.
//       Thank you Ulf Adams.
//
//    2) The original java sources were converted to a rough draft of
//       scala code using the service at URL: javatoscala.com.
//
//       The raw conversion did not compile and contained bugs due
//       to the handling of break and return statements, but it saved
//       days, if not weeks, of effort.
//
//       Thank you javatoscala.com.
//
//    3) All additional work, including introduced bugs,  is an original
//       contribution to Scala Native development.

package scala.scalanative
package runtime
package ieee754tostring.ryu

import RyuRoundingMode._

object RyuFloat {

  final val FLOAT_MANTISSA_BITS = 23

  final val FLOAT_MANTISSA_MASK = (1 << FLOAT_MANTISSA_BITS) - 1

  final val FLOAT_EXPONENT_BITS = 8

  final val FLOAT_EXPONENT_MASK = (1 << FLOAT_EXPONENT_BITS) - 1

  final val FLOAT_EXPONENT_BIAS = (1 << (FLOAT_EXPONENT_BITS - 1)) - 1

  final val LOG10_2_DENOMINATOR = 10000000L

  final val LOG10_2_NUMERATOR = (LOG10_2_DENOMINATOR * Math.log10(2)).toLong

  final val LOG10_5_DENOMINATOR = 10000000L

  final val LOG10_5_NUMERATOR = (LOG10_5_DENOMINATOR * Math.log10(5)).toLong

  final val LOG2_5_DENOMINATOR = 10000000L

  final val LOG2_5_NUMERATOR =
    (LOG2_5_DENOMINATOR * (Math.log(5) / Math.log(2))).toLong

  final val POW5_BITCOUNT = 61

  final val POW5_HALF_BITCOUNT = 31

// Tell scalafmt to retain POW5_ARRAY_NCOL column format for human readability.
// format: off

  final val POW5_ARRAY_NCOL = 2

  // For origin of these magic values,
  // see ""Porting Note for POW5_SPLIT & POW5_INV_SPIT arrays" at top of
  // RyuDouble.scala.

  final val POW5_SPLIT = scala.Array(
      536870912, 0,
      671088640, 0,
      838860800, 0,
      1048576000, 0,
      655360000, 0,
      819200000, 0,
      1024000000, 0,
      640000000, 0,
      800000000, 0,
      1000000000, 0,
      625000000, 0,
      781250000, 0,
      976562500, 0,
      610351562, 1073741824,
      762939453, 268435456,
      953674316, 872415232,
      596046447, 1619001344,
      745058059, 1486880768,
      931322574, 1321730048,
      582076609, 289210368,
      727595761, 898383872,
      909494701, 1659850752,
      568434188, 1305842176,
      710542735, 1632302720,
      888178419, 1503507488,
      555111512, 671256724,
      693889390, 839070905,
      867361737, 2122580455,
      542101086, 521306416,
      677626357, 1725374844,
      847032947, 546105819,
      1058791184, 145761362,
      661744490, 91100851,
      827180612, 1187617888,
      1033975765, 1484522360,
      646234853, 1196261931,
      807793566, 2032198326,
      1009741958, 1466506084,
      631088724, 379695390,
      788860905, 474619238,
      986076131, 1130144959,
      616297582, 437905143,
      770371977, 1621123253,
      962964972, 415791331,
      601853107, 1333611405,
      752316384, 1130143345,
      940395480, 1412679181
    )

  final val POW5_INV_BITCOUNT = 59

  final val POW5_INV_HALF_BITCOUNT = 31

  // For origin of these magic values,
  // see ""Porting Note for POW5_SPLIT & POW5_INV_SPIT arrays" at top of
  // RyuDouble.scala.

  final val POW5_INV_SPLIT = scala.Array(
      268435456, 1,
      214748364, 1717986919,
      171798691, 1803886265,
      137438953, 1013612282,
      219902325, 1192282922,
      175921860, 953826338,
      140737488, 763061070,
      225179981, 791400982,
      180143985, 203624056,
      144115188, 162899245,
      230584300, 1978625710,
      184467440, 1582900568,
      147573952, 1266320455,
      236118324, 308125809,
      188894659, 675997377,
      151115727, 970294631,
      241785163, 1981968139,
      193428131, 297084323,
      154742504, 1955654377,
      247588007, 1840556814,
      198070406, 613451992,
      158456325, 61264864,
      253530120, 98023782,
      202824096, 78419026,
      162259276, 1780722139,
      259614842, 1990161963,
      207691874, 733136111,
      166153499, 1016005619,
      265845599, 337118801,
      212676479, 699191770,
      170141183, 988850146
    )

// format: on

  def floatToString(value: Float, roundingMode: RyuRoundingMode): String = {

    // Step 1: Decode the floating point number, and unify normalized and
    // subnormal cases.
    // First, handle all the trivial cases.
    if (value.isNaN) return "NaN"
    if (value == Float.PositiveInfinity) return "Infinity"
    if (value == Float.NegativeInfinity) return "-Infinity"
    val bits = java.lang.Float.floatToIntBits(value)
    if (bits == 0) return "0.0"
    if (bits == 0x80000000) return "-0.0"
    // Otherwise extract the mantissa and exponent bits and run the full
    // algorithm.
    val ieeeExponent = (bits >> FLOAT_MANTISSA_BITS) & FLOAT_EXPONENT_MASK
    val ieeeMantissa = bits & FLOAT_MANTISSA_MASK
    // By default, the correct mantissa starts with a 1, except for
    // denormal numbers.
    var e2 = 0
    var m2 = 0
    if (ieeeExponent == 0) {
      e2 = 1 - FLOAT_EXPONENT_BIAS - FLOAT_MANTISSA_BITS
      m2 = ieeeMantissa
    } else {
      e2 = ieeeExponent - FLOAT_EXPONENT_BIAS - FLOAT_MANTISSA_BITS
      m2 = ieeeMantissa | (1 << FLOAT_MANTISSA_BITS)
    }
    val sign = bits < 0

    // Step 2: Determine the interval of legal decimal representations.
    val even = (m2 & 1) == 0
    val mv   = 4 * m2
    val mp   = 4 * m2 + 2
    val mm = 4 * m2 -
      (if ((m2 != (1L << FLOAT_MANTISSA_BITS)) || (ieeeExponent <= 1)) 2
       else 1)
    e2 -= 2

    // Step 3: Convert to a decimal power base using 128-bit arithmetic.
    // -151 = 1 - 127 - 23 - 2 <= e_2 - 2 <= 254 - 127 - 23 - 2 = 102
    var dp                = 0
    var dv                = 0
    var dm                = 0
    var e10               = 0
    var dpIsTrailingZeros = false
    var dvIsTrailingZeros = false
    var dmIsTrailingZeros = false
    var lastRemovedDigit  = 0
    if (e2 >= 0) {
      // Compute m * 2^e_2 / 10^q = m * 2^(e_2 - q) / 5^q
      val q = (e2 * LOG10_2_NUMERATOR / LOG10_2_DENOMINATOR).toInt
      val k = POW5_INV_BITCOUNT + pow5bits(q) - 1
      val i = -e2 + q + k
      dv = mulPow5InvDivPow2(mv, q, i).toInt
      dp = mulPow5InvDivPow2(mp, q, i).toInt
      dm = mulPow5InvDivPow2(mm, q, i).toInt
      if (q != 0 && ((dp - 1) / 10 <= dm / 10)) {
        // 32-bit arithmetic is faster even on 64-bit machines.
        val l = POW5_INV_BITCOUNT + pow5bits(q - 1) - 1
        lastRemovedDigit =
          (mulPow5InvDivPow2(mv, q - 1, -e2 + q - 1 + l) % 10).toInt
      }
      // We need to know one removed digit even if we are not going to loop
      // below. We could use
      // q = X - 1 above, except that would require 33 bits for the result,
      // and we've found that
      // 32-bit arithmetic is faster even on 64-bit machines
      e10 = q
      dpIsTrailingZeros = pow5Factor(mp) >= q
      dvIsTrailingZeros = pow5Factor(mv) >= q
      dmIsTrailingZeros = pow5Factor(mm) >= q
    } else {
      // Compute m * 5^(-e_2) / 10^q = m * 5^(-e_2 - q) / 2^q
      val q = (-e2 * LOG10_5_NUMERATOR / LOG10_5_DENOMINATOR).toInt
      val i = -e2 - q
      val k = pow5bits(i) - POW5_BITCOUNT
      var j = q - k
      dv = mulPow5divPow2(mv, i, j).toInt
      dp = mulPow5divPow2(mp, i, j).toInt
      dm = mulPow5divPow2(mm, i, j).toInt
      if (q != 0 && ((dp - 1) / 10 <= dm / 10)) {
        j = q - 1 - (pow5bits(i + 1) - POW5_BITCOUNT)
        lastRemovedDigit = (mulPow5divPow2(mv, i + 1, j) % 10).toInt
      }
      e10 = q + e2 // Note: e2 and e10 are both negative here.
      dpIsTrailingZeros = 1 >= q
      dvIsTrailingZeros = (q < FLOAT_MANTISSA_BITS) &&
        (mv & ((1 << (q - 1)) - 1)) == 0
      dmIsTrailingZeros = (if (mm % 2 == 1) 0 else 1) >= q
    }

    // Step 4: Find the shortest decimal representation in the interval of
    // legal representations.
    //
    // We do some extra work here in order to follow Float/Double.toString
    // semantics. In particular, that requires printing in scientific format
    // if and only if the exponent is between -3 and 7, and it requires
    // printing at least two decimal digits.
    //
    // Above, we moved the decimal dot all the way to the right, so now we
    // need to count digits to
    // figure out the correct exponent for scientific notation.
    val dplength = decimalLength(dp)
    var exp      = e10 + dplength - 1
    // Float.toString semantics requires using scientific notation if and
    // only if outside this range.
    val scientificNotation = !((exp >= -3) && (exp < 7))
    var removed            = 0
    if (dpIsTrailingZeros && !roundingMode.acceptUpperBound(even)) {
      dp -= 1
    }

    var done = false // workaround break in .java source

    while ((dp / 10 > dm / 10) && !done) {
      if ((dp < 100) && scientificNotation) {
        // We print at least two digits, so we might as well stop now.
        done = true
      } else {
        dmIsTrailingZeros &= dm % 10 == 0
        dp /= 10
        lastRemovedDigit = dv % 10
        dv /= 10
        dm /= 10
        removed += 1
      }
    }
    if (dmIsTrailingZeros && roundingMode.acceptLowerBound(even)) {
      var done = false // workaround break in .java source
      while ((dm % 10 == 0) && !done) {
        if ((dp < 100) && scientificNotation) {
          // We print at least two digits, so we might as well stop now.
          done = true
        } else {
          dp /= 10
          lastRemovedDigit = dv % 10
          dv /= 10
          dm /= 10
          removed += 1
        }
      }
    }
    if (dvIsTrailingZeros && (lastRemovedDigit == 5) && (dv % 2 == 0)) {
      // Round down not up if the number ends in X50000 and the number is even.
      lastRemovedDigit = 4
    }
    var output = dv +
      (if ((dv == dm &&
           !(dmIsTrailingZeros && roundingMode.acceptLowerBound(even))) ||
           (lastRemovedDigit >= 5)) 1
       else 0)
    val olength = dplength - removed

    // Step 5: Print the decimal representation.
    // We follow Float.toString semantics here.
    val result = scala.Array.ofDim[Char](15)
    var index  = 0
    if (sign) {
      result(index) = '-'
      index += 1
    }
    if (scientificNotation) {
      for (i <- 0 until olength - 1) {
        val c = output % 10
        output /= 10
        result(index + olength - i) = ('0' + c).toChar
      }
      result(index) = ('0' + output % 10).toChar
      result(index + 1) = '.'
      index += olength + 1
      if (olength == 1) {
        result(index) = '0'
        index += 1
      }
      // Print 'E', the exponent sign, and the exponent, which has at most
      // two digits.
      result(index) = 'E'
      index += 1
      if (exp < 0) {
        result(index) = '-'
        index += 1
        exp = -exp
      }
      if (exp >= 10) {
        result(index) = ('0' + exp / 10).toChar
        index += 1
      }
      result(index) = ('0' + exp % 10).toChar
      index += 1
    } else {
      // Otherwise follow the Java spec for values in the interval [1E-3, 1E7).
      if (exp < 0) {
        // Decimal dot is before any of the digits.
        result(index) = '0'
        index += 1
        result(index) = '.'
        index += 1
        var i = -1
        while (i > exp) {
          result(index) = '0'
          index += 1
          i -= 1
        }
        val current = index
        for (i <- 0 until olength) {
          result(current + olength - i - 1) = ('0' + output % 10).toChar
          output /= 10
          index += 1
        }
      } else if (exp + 1 >= olength) {
        for (i <- 0 until olength) {
          result(index + olength - i - 1) = ('0' + output % 10).toChar
          output /= 10
        }
        index += olength
        for (i <- olength until exp + 1) {
          result(index) = '0'
          index += 1
        }
        result(index) = '.'
        index += 1
        result(index) = '0'
        index += 1
      } else {
        // Decimal dot is somewhere between the digits.
        var current = index + 1
        for (i <- 0 until olength) {
          if (olength - i - 1 == exp) {
            result(current + olength - i - 1) = '.'
            current -= 1
          }
          result(current + olength - i - 1) = ('0' + output % 10).toChar
          output /= 10
        }
        index += olength + 1
      }
    }
    new String(result, 0, index)
  }

  private def pow5bits(e: Int): Int =
    if (e == 0) 1
    else
      ((e * LOG2_5_NUMERATOR + LOG2_5_DENOMINATOR - 1)
        / LOG2_5_DENOMINATOR).toInt

  /**
   * Returns the exponent of the largest power of 5 that divides the given
   * value, i.e., returns i such that value = 5^i * x, where x is an integer.
   */
  private def pow5Factor(_value: Int): Int = {
    var value = _value
    var count = 0
    while (value > 0) {
      if (value % 5 != 0) {
        return count
      }
      value /= 5
      count += 1
    }
    throw new IllegalArgumentException("" + value)
  }

  /**
   * Compute the exact result of:
   *   [m * 5^(-e_2) / 10^q] = [m * 5^(-e_2 - q) / 2^q]
   *   = [m * [5^(p - q)/2^k] / 2^(q - k)] = [m * POW5[i] / 2^j].
   */
  private def mulPow5divPow2(m: Int, i: Int, j: Int): Long = {
    if (j - POW5_HALF_BITCOUNT < 0) {
      throw new IllegalArgumentException()
    }
    val bits0 = m * POW5_SPLIT((i * POW5_ARRAY_NCOL) + 0).toLong
    val bits1 = m * POW5_SPLIT((i * POW5_ARRAY_NCOL) + 1).toLong
    (bits0 + (bits1 >> POW5_HALF_BITCOUNT)) >> (j - POW5_HALF_BITCOUNT)
  }

  /**
   * Compute the exact result of:
   *   [m * 2^p / 10^q] = [m * 2^(p - q) / 5 ^ q]
   *   = [m * [2^k / 5^q] / 2^-(p - q - k)] = [m * POW5_INV[q] / 2^j].
   */
  private def mulPow5InvDivPow2(m: Int, q: Int, j: Int): Long = {
    if (j - POW5_INV_HALF_BITCOUNT < 0) {
      throw new IllegalArgumentException()
    }
    val bits0 = m * POW5_INV_SPLIT((q * POW5_ARRAY_NCOL) + 0).toLong
    val bits1 = m * POW5_INV_SPLIT((q * POW5_ARRAY_NCOL) + 1).toLong
    (bits0 + (bits1 >> POW5_INV_HALF_BITCOUNT)) >> (j - POW5_INV_HALF_BITCOUNT)
  }

  private def decimalLength(v: Int): Int = {
    var length = 10
    var factor = 1000000000
    var done   = false

    while ((length > 0) && !done) {
      if (v >= factor) {
        done = true
      } else {
        factor /= 10
        length -= 1
      }
    }
    length
  }

}
