/*
 * Written by Doug Lea with assistance from members of JCP JSR-166
 * Expert Group and released to the public domain, as explained at
 * http://creativecommons.org/publicdomain/zero/1.0/
 */

/* See SN Repository git history for Scala Native additions.
 * The Java 17 JEP356 work to extend RandomGenerator caused many changes.
 *
 * Devo note:
 *   A bold developer, with too much time on their hands, could follow the
 *   Scala.js PR #5142 example and eliminate almost all of this file,
 *   letting transitive inheritance from Random to RandomGenerator
 *   do most of the work.
 *
 *   This first JEP 356 Evolution uses overrides to preserve historical
 *   behavior.
 */

package java.util.concurrent

import java.util._
import java.util.function._
import java.util.random.RandomSupport
import java.util.stream._
import java.util.concurrent.atomic._

import scala.scalanative.annotation.safePublish
import scala.scalanative.meta.LinktimeInfo

@SerialVersionUID(-5851777807851030925L)
object ThreadLocalRandom {
  private def mix64(z0: Long) = {
    var z = z0
    z = (z ^ (z >>> 33)) * 0xff51afd7ed558ccdL
    z = (z ^ (z >>> 33)) * 0xc4ceb9fe1a85ec53L
    z ^ (z >>> 33)
  }

  private def mix32(z0: Long) = {
    var z = z0
    z = (z ^ (z >>> 33)) * 0xff51afd7ed558ccdL
    (((z ^ (z >>> 33)) * 0xc4ceb9fe1a85ec53L) >>> 32).toInt
  }

  private[concurrent] def localInit(): Unit = {
    val p = probeGenerator.addAndGet(PROBE_INCREMENT)
    val probe =
      if (p == 0) 1
      else p // skip 0
    val seed = mix64(seeder.getAndAdd(SEEDER_INCREMENT))
    val t = Thread.currentThread()
    t.threadLocalRandomSeed = seed
    t.threadLocalRandomProbe = probe
  }

  def current(): ThreadLocalRandom = {
    if (Thread.currentThread().threadLocalRandomProbe == 0)
      localInit()
    instance
  }

  /** Spliterator for int streams. We multiplex the four int versions into one
   *  class by treating a bound less than origin as unbounded, and also by
   *  treating "infinite" as equivalent to Long.MAX_VALUE. For splits, it uses
   *  the standard divide-by-two approach. The long and double versions of this
   *  class are identical except for types.
   */
  final private class RandomIntsSpliterator(
      var index: Long,
      fence: Long,
      origin: Int,
      bound: Int
  ) extends Spliterator.OfInt {
    override def trySplit(): ThreadLocalRandom.RandomIntsSpliterator = {
      val i = index
      val m = (i + fence) >>> 1
      if (m <= i) null
      else {
        index = m
        new ThreadLocalRandom.RandomIntsSpliterator(i, m, origin, bound)
      }
    }

    override def estimateSize(): Long = fence - index

    override def characteristics(): Int =
      RandomSupport.randomStreamCharacteristics

    override def tryAdvance(consumer: IntConsumer): Boolean = {
      if (consumer == null)
        throw new NullPointerException

      if (index < fence) {
        consumer.accept(
          ThreadLocalRandom.current().internalNextInt(origin, bound)
        )
        index += 1
        return true
      }
      false
    }

    override def forEachRemaining(consumer: IntConsumer): Unit = {
      if (consumer == null)
        throw new NullPointerException

      if (index < fence) {
        var i = index

        index = fence
        val rng = ThreadLocalRandom.current()

        while ({
          consumer.accept(rng.internalNextInt(origin, bound))
          i += 1
          i < fence
        }) ()
      }
    }
  }

  final private class RandomLongsSpliterator(
      var index: Long,
      fence: Long,
      origin: Long,
      bound: Long
  ) extends Spliterator.OfLong {

    override def trySplit(): ThreadLocalRandom.RandomLongsSpliterator = {
      val i = index
      val m = (i + fence) >>> 1
      if (m <= index) null
      else {
        index = m
        new ThreadLocalRandom.RandomLongsSpliterator(i, m, origin, bound)
      }
    }

    override def estimateSize(): Long = fence - index
    override def characteristics(): Int =
      RandomSupport.randomStreamCharacteristics

    override def tryAdvance(consumer: LongConsumer): Boolean = {
      if (consumer == null)
        throw new NullPointerException

      if (index < fence) {
        consumer.accept(
          ThreadLocalRandom.current().internalNextLong(origin, bound)
        )
        index += 1
        return true
      }
      false
    }

    override def forEachRemaining(consumer: LongConsumer): Unit = {
      if (consumer == null)
        throw new NullPointerException

      if (index < fence) {
        val rng = ThreadLocalRandom.current()

        var i = index
        index = fence
        while ({
          consumer.accept(rng.internalNextLong(origin, bound))
          i += 1
          i < fence
        }) ()
      }
    }
  }

  final private class RandomDoublesSpliterator(
      var index: Long,
      fence: Long,
      origin: Double,
      bound: Double
  ) extends Spliterator.OfDouble {

    override def trySplit(): ThreadLocalRandom.RandomDoublesSpliterator = {
      val m = (index + fence) >>> 1
      if (m <= index) null
      else {
        val i = index
        index = m
        new ThreadLocalRandom.RandomDoublesSpliterator(i, m, origin, bound)
      }
    }
    override def estimateSize(): Long = fence - index
    override def characteristics(): Int =
      RandomSupport.randomStreamCharacteristics

    override def tryAdvance(consumer: DoubleConsumer): Boolean = {
      if (consumer == null)
        throw new NullPointerException

      if (index < fence) {
        consumer.accept(
          ThreadLocalRandom.current().internalNextDouble()(origin, bound)
        )
        index += 1
        return true
      }
      false
    }
    override def forEachRemaining(consumer: DoubleConsumer): Unit = {
      if (consumer == null)
        throw new NullPointerException

      if (index < fence) {
        val rng = ThreadLocalRandom.current()
        var i = index
        index = fence
        while ({
          consumer.accept(rng.internalNextDouble()(origin, bound))
          i += 1
          i < fence
        }) ()
      }
    }
  }

  private[concurrent] def getProbe(): Int =
    Thread.currentThread().threadLocalRandomProbe

  private[concurrent] def advanceProbe(probe0: Int) = {
    var probe = probe0
    probe ^= probe << 13 // xorshift
    probe ^= probe >>> 17
    probe ^= probe << 5
    Thread.currentThread().threadLocalRandomProbe = probe
    probe
  }

  private[concurrent] def nextSecondarySeed(): Int = {
    val t = Thread.currentThread()
    var r: Int = t.threadLocalRandomSecondarySeed
    if (r != 0) {
      r ^= r << 13
      r ^= r >>> 17
      r ^= r << 5
    } else {
      r = mix32(seeder.getAndAdd(SEEDER_INCREMENT))
      if (r == 0) r = 1 // avoid zero
    }
    // U.putInt(t, SECONDARY, r)
    t.threadLocalRandomSecondarySeed = r
    r
  }

  private[concurrent] def eraseThreadLocals(thread: Thread): Unit = {
    thread.threadLocals = null
    thread.inheritableThreadLocals = null
  }

  private val GAMMA = 0x9e3779b97f4a7c15L

  private val PROBE_INCREMENT = 0x9e3779b9
  private val SEEDER_INCREMENT = 0xbb67ae8584caa73bL

  private val DOUBLE_UNIT = 1.0 / (1L << 53)
  private val FLOAT_UNIT = 1.0f / (1 << 24)

  // IllegalArgumentException messages
  private[concurrent] val BAD_BOUND = "bound must be positive"
  private[concurrent] val BAD_RANGE = "bound must be greater than origin"
  private[concurrent] val BAD_SIZE = "size must be non-negative"

  private val nextLocalGaussian = new ThreadLocal[java.lang.Double]

  @safePublish
  private val probeGenerator = new AtomicInteger

  @safePublish
  private[concurrent] val instance = new ThreadLocalRandom

  private val seeder = new AtomicLong(
    mix64(System.currentTimeMillis()) ^ mix64(System.nanoTime())
  )
}

@SerialVersionUID(-5851777807851030925L)
class ThreadLocalRandom private () extends Random {

  private[concurrent] var initialized = true

  override def setSeed(seed: Long): Unit = { // only allow call from super() constructor
    if (initialized)
      throw new UnsupportedOperationException
  }
  final private[concurrent] def nextSeed(): Long = {
    val t = Thread.currentThread()
    t.threadLocalRandomSeed +=
      ThreadLocalRandom.GAMMA // read and update per-thread seed
    t.threadLocalRandomSeed
  }

  override protected def next(bits: Int): Int = nextInt() >>> (32 - bits)

  final private[concurrent] def internalNextLong(origin: Long, bound: Long) = {
    var r = ThreadLocalRandom.mix64(nextSeed())
    if (origin < bound) {
      val n = bound - origin
      val m = n - 1
      if ((n & m) == 0L) { // power of two
        r = (r & m) + origin
      } else if (n > 0L) { // reject over-represented candidates
        var u = r >>> 1 // ensure nonnegative
        r = u % n
        while ((u + m - r) < 0L) { // rejection check
          // retry
          u = ThreadLocalRandom.mix64(nextSeed()) >>> 1
        }
        r += origin
      } else { // range not representable as long
        while ({ r < origin || r >= bound }) {
          r = ThreadLocalRandom.mix64(nextSeed())
        }
      }
    }
    r
  }

  final private[concurrent] def internalNextInt(origin: Int, bound: Int) = {
    var r = ThreadLocalRandom.mix32(nextSeed())
    if (origin < bound) {
      val n = bound - origin
      val m = n - 1
      if ((n & m) == 0) r = (r & m) + origin
      else if (n > 0) {
        var u = r >>> 1
        r = u % n
        while ((u + m - r) < 0)
          u = ThreadLocalRandom.mix32(nextSeed()) >>> 1
        r += origin
      } else
        while ({ r < origin || r >= bound }) {
          r = ThreadLocalRandom.mix32(nextSeed())
        }
    }
    r
  }

  final private[concurrent] def internalNextDouble()(
      origin: Double,
      bound: Double
  ) = {
    var r = (nextLong() >>> 11) * ThreadLocalRandom.DOUBLE_UNIT
    if (origin < bound) {
      r = r * (bound - origin) + origin
      if (r >= bound) { // correct for rounding
        r = java.lang.Double.longBitsToDouble(
          java.lang.Double.doubleToLongBits(bound) - 1
        )
      }
    }
    r
  }

  override def nextInt(): Int = ThreadLocalRandom.mix32(nextSeed())

  /* Without the override the pre-JEP356 ThreadLocalRandom Test fails in
   * CI 32 bit "Test cross-compilation (linux-x86, 2.13)". It appears that
   * the "next" Double is exactly 1.7976931348623157E308 which is _outside_
   * the exclusive bound of (Scala) Double.MaxValue. Oops!
   *
   * The 64 bit "Test cross-compilation (linux-arm64, 2.13)" succeeds.
   * It may be that the "exactly on the exclusion barrier" value is never
   * getting generated.
   *
   * Try using the historical values on 32-bit systems otherwise use the
   * RandomGenerator method. This introduces an architectural difference
   * _within_ ThreadLocalRandom, but maintains consistency _across_ 64-bit
   * systems. The latter alternative should prove to be be less astonishing
   * as 32-bit systems fade away.
   */
  override def nextDouble(): Double = {
    if (!LinktimeInfo.is32BitPlatform) {
      super.nextDouble()
    } else {
      (ThreadLocalRandom.mix64(nextSeed()) >>> 11) *
        ThreadLocalRandom.DOUBLE_UNIT
    }
  }

  override def nextLong(): Long = ThreadLocalRandom.mix64(nextSeed())
}
