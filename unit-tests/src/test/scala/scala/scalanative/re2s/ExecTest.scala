package scala.scalanative
package re2s

import java.io.InputStreamReader
import java.io.File
import java.io.FileInputStream
import java.util
import java.util.zip.GZIPInputStream
import java.util.{Arrays, Collections}

import scala.util.control.NonFatal
import scala.util.control.Breaks._

import ScalaTestCompat.fail

// TestRE2 tests this package's regexp API against test cases
// considered during (C++) RE2's exhaustive tests, which run all possible
// regexps over a given set of atoms and operators, up to a given
// complexity, over all possible strings over a given alphabet,
// up to a given size.  Rather than try to link with RE2, we read a
// log file containing the test cases and the expected matches.
// The log file, re2.txt, is generated by running 'make exhaustive-log'
// in the open source RE2 distribution.  http://code.google.com/p/re2/
//
// The test file format is a sequence of stanzas like:
//
//      strings
//      "abc"
//      "123x"
//      regexps
//      "[a-z]+"
//      0-3;0-3
//      -;-
//      "([0-9])([0-9])([0-9])"
//      -;-
//      -;0-3 0-1 1-2 2-3
//
// The stanza begins by defining a set of strings, quoted
// using Go double-quote syntax, one per line.  Then the
// regexps section gives a sequence of regexps to run on
// the strings.  In the block that follows a regexp, each line
// gives the semicolon-separated match results of running
// the regexp on the corresponding string.
// Each match result is either a single -, meaning no match, or a
// space-separated sequence of pairs giving the match and
// submatch indices.  An unmatched subexpression formats
// its pair as a single - (not illustrated above).  For now
// each regexp run produces two match results, one for a
// ``full match'' that restricts the regexp to matching the entire
// string or nothing, and one for a ``partial match'' that gives
// the leftmost first match found in the string.
//
// Lines beginning with # are comments.  Lines beginning with
// a capital letter are test names printed during RE2's test suite
// and are echoed into t but otherwise ignored.
//
// At time of writing, re2.txt is 32 MB but compresses to 760 kB,
// so we store re2.txt.gz in the repository and decompress it on the fly.

object ExecTestSuite extends tests.Suite {

  test("ExamplesInDocumentation") {
    val re = RE2.compile("(?i:co(.)a)")
    assert(
      Array(
        "Copa", "coba").deep == re.findAll("Copacobana", 10).toArray.deep, "assertion #1")
    val x = re.findAllSubmatch("Copacobana", 100)
    assert(Array("Copa", "p").deep == x.get(0).deep, "Assertion #2")
    assert(Array("coba", "b").deep == x.get(1).deep, "Assertion #3")
  }

  test("RE2Search") { // 1832pass/20failed
    testRE2("re2-search.txt")
  }

  test("RE2Exhaustive") { // >100failed
    testRE2("re2-exhaustive.txt.gz") // takes about 30s
  }

  def testRE2(_file: String) = {
    var file = _file
    var in : java.io.InputStream =
      new FileInputStream(new File("unit-tests/src/test/resources/" + file))
    // TODO(adonovan): call in.close() on all paths.
    if (file.endsWith(".gz")) {
      in = new GZIPInputStream(in)
      file = file.substring(0, file.length - ".gz".length) // for errors
    }
    var lineno  = 0
    val r       = new UNIXBufferedReader(new InputStreamReader(in, "UTF-8"))
    val strings = new util.ArrayList[String]
    var input   = 0
    // next index within strings to read
    var inStrings    = false
    var re: RE2      = null
    var refull: RE2  = null
    var nfail        = 0
    var ncase        = 0
    var line: String = null
    while ({ line = r.readLine; line != null }) breakable {
      lineno += 1
      if (line.isEmpty)
        fail("%s:%d: unexpected blank line".format(file, lineno))
      val first = line.charAt(0)
      if (first == '#') break
      if ('A' <= first && first <= 'Z') { // Test name.
        System.err.println(line)
      } else if (line == "strings") {
        if (input < strings.size)
          fail(
            "%s:%d: out of sync: have %d strings left"
              .format(file, lineno, strings.size - input))
        strings.clear()
        inStrings = true
      } else if (line == "regexps") inStrings = false
      else if (first == '"') {
        var q: String = null
        try q = Strconv.unquote(line)
        catch {
          case NonFatal(e) =>
            // Fatal because we'll get out of sync.
            fail(
              "%s:%d: unquote %s: %s"
                .format(file, lineno, line, e.getMessage))
            q = null // unreachable

        }
        if (inStrings) {
          strings.add(q)
          break
        }

        // Is a regexp.
        re = null
        refull = null
        try {
          re = RE2.compile(q)
        } catch {
          case NonFatal(e) =>
            // (handle compiler panic too)
            if (e.getMessage.startsWith("Illegal/unsupported escape sequence")) { // We don't and likely never will support \C; keep going.
              break
            }
            System.err.println(
              "%s:%d: compile %s: %s\n"
                .format(file, lineno, q, e.getMessage))
            nfail += 1
            if (nfail >= 100) fail("stopping after " + nfail + " errors")
            break
        }
        val full = "\\A(?:" + q + ")\\z"
        try refull = RE2.compile(full)
        catch {
          case NonFatal(e) =>
            // Fatal because q worked, so this should always work.
            fail(
              "%s:%d: compile full %s: %s"
                .format(file, lineno, full, e.getMessage))
        }
        input = 0
      } else if (first == '-' || '0' <= first && first <= '9') { // A sequence of match results.
        ncase += 1
        if (re == null) { // Failed to compile: skip results.
          break
        }
        if (input >= strings.size)
          fail("%s:%d: out of sync: no input remaining".format(file, lineno))
        val text = strings.get(input)
        input += 1
        val multibyte = !isSingleBytes(text)
        if (multibyte && re.toString.contains("\\B")) { // C++ RE2's \B considers every position in the input, which
          // is a stream of bytes, so it sees 'not word boundary' in the
          // middle of a rune.  But this package only considers whole
          // runes, so it disagrees.  Skip those cases.
          break
        }
        val res = line.split(";")
        if (res.length != 4)
          fail(
            "%s:%d: have %d test results, want %d"
              .format(file, lineno, res.length, 4))
        var i = 0
        while (i < 4) {
          val partial = (i & 1) != 0
          val longest = (i & 2) != 0
          val regexp =
            if (partial) re
            else refull
          regexp.longest = longest
          var have = regexp.findSubmatchIndex(text) // UTF-16 indices
          if (multibyte && have != null) { // The testdata uses UTF-8 indices, but we're using the UTF-16 API.
            // Perhaps we should use the UTF-8 RE2 API?
            have = utf16IndicesToUtf8(have, text)
          }
          val want = parseResult(file, lineno, res(i)) // UTF-8 indices
          if (!Arrays.equals(want, have)) {
            // we use \P{Upper} the test case uses [[:upper]]
            if (line.contains("[[:")) {
              System.err.println(
                "%s:%d: %s[partial=%b,longest=%b].findSubmatchIndex(%s) = %s, want %s\n"
                  .format(file,
                          lineno,
                          re,
                          partial,
                          longest,
                          text,
                          util.Arrays.toString(have),
                          util.Arrays.toString(want)))
              nfail += 1
              if (nfail >= 100) fail("stopping after " + nfail + " errors")
            }
            break
          }
          regexp.longest = longest
          val b = regexp.match_(text)
          if (b != (want != null)) {
            System.err.println(
              "%s:%d: %s[partial=%b,longest=%b].match(%s) = %b, want %b\n"
                .format(file, lineno, re, partial, longest, text, b, !b))
            nfail += 1
            if (nfail >= 100)
              fail("stopping after " + nfail + " errors")
            break
          }

          i += 1
        }
      } else fail("%s:%d: out of sync: %s\n".format(file, lineno, line))
    }
    if (input < strings.size)
      fail(
        "%s:%d: out of sync: have %d strings left at EOF"
          .format(file, lineno, strings.size - input))
    if (nfail > 0) fail("Of %d cases tested, %d failed".format(ncase, nfail))
    else System.err.println("%d cases tested\n".format(ncase))
  }

  // Returns true iff there are no runes with multibyte UTF-8 encodings in s.
  private def isSingleBytes(s: String): Boolean = {
    var i   = 0
    val len = s.length
    while (i < len) {
      if (s.charAt(i) >= 0x80) return false
      i += 1
    }
    true
  }

  // Convert |idx16|, which are Java (UTF-16) string indices, into the
  // corresponding indices in the UTF-8 encoding of |text|.
  private def utf16IndicesToUtf8(idx16: Array[Int], text: String) =
    try {
      val idx8 = new Array[Int](idx16.length)
      var i    = 0
      while (i < idx16.length) {
        idx8(i) = text.substring(0, idx16(i)).getBytes("UTF-8").length
        i += 1
      }
      idx8
    } catch {
      case e: java.io.UnsupportedEncodingException =>
        throw new IllegalStateException(e)
    }

  private def parseResult(
      file: String,
      lineno: Int,
      res: String): Array[Int] = { // A single - indicates no match.
    if (res == "-") return null
    // Otherwise, a space-separated list of pairs.
    var n = 1

    // TODO(adonovan): is this safe or must we decode UTF-16?
    val len = res.length
    var j   = 0
    while (j < len) {
      if (res.charAt(j) == ' ') n += 1
      j += 1
    }
    val out = new Array[Int](2 * n)
    var i   = 0
    n = 0
    j = 0
    while (j <= len) {
      if (j == len || res.charAt(j) == ' ') { // Process a single pair.  - means no submatch.
        val pair = res.substring(i, j)
        if (pair == "-") {
          out({
            n += 1; n - 1
          }) = -1
          out({
            n += 1; n - 1
          }) = -1
        } else {
          val k = pair.indexOf('-')
          if (k < 0) fail("%s:%d: invalid pair %s".format(file, lineno, pair))
          var lo = -1
          var hi = -2
          try {
            lo = Integer.valueOf(pair.substring(0, k))
            hi = Integer.valueOf(pair.substring(k + 1))
          } catch {
            case e: NumberFormatException =>
            /* fall through */
          }
          if (lo > hi) fail("%s:%d: invalid pair %s".format(file, lineno, pair))
          out(n) = lo
          n += 1
          out(n) = hi
          n += 1
        }
        i = j + 1
      }

      j += 1
    }
    out
  }

  // The testFowler* methods run this package's regexp API against the
  // POSIX regular expression tests collected by Glenn Fowler at
  // http://www2.research.att.com/~gsf/testregex/.

  test("FowlerBasic") {
    testFowler("basic.dat")
  }

  test("FowlerNullSubexpr") {
    testFowler("nullsubexpr.dat")
  }

  test("FowlerRepetition") {
    testFowler("repetition.dat")
  }

  private val NOTAB = RE2.compilePOSIX("[^\t]+")

  def testFowler(file: String): Unit = {

    var in : java.io.InputStream =
      new FileInputStream(new File("unit-tests/src/test/resources/" + file))

    val r            = new UNIXBufferedReader(new InputStreamReader(in, "UTF-8"))
    var lineno       = 0
    var nerr         = 0
    var line: String = null
    var lastRegexp   = ""
    while ({ line = r.readLine; line != null }) breakable {
      lineno += 1
      // if (line.isEmpty()) {
      //   fail(String.format("%s:%d: unexpected blank line", file, lineno));
      // }
      // http://www2.research.att.com/~gsf/man/man1/testregex.html
      //
      // INPUT FORMAT
      //   Input lines may be blank, a comment beginning with #, or a test
      //   specification. A specification is five fields separated by one
      //   or more tabs. NULL denotes the empty string and NULL denotes the
      //   0 pointer.
      if (line.isEmpty || line.charAt(0) == '#') break
      val field = NOTAB.findAll(line, -1)
      var i     = 0
      while (i < field.size) {
        if (field.get(i) == "NULL") field.set(i, "")
        if (field.get(i) == "NIL") {
          System.err.println("%s:%d: skip: %s\n".format(file, lineno, line))
          break
        }

        i += 1
      }
      if (field.isEmpty) break
      //   Field 1: the regex(3) flags to apply, one character per
      //   REG_feature flag. The test is skipped if REG_feature is not
      //   supported by the implementation. If the first character is
      //   not [BEASKLP] then the specification is a global control
      //   line. One or more of [BEASKLP] may be specified; the test
      //   will be repeated for each mode.
      //     B        basic                   BRE     (grep, ed, sed)
      //     E        REG_EXTENDED            ERE     (egrep)
      //     A        REG_AUGMENTED           ARE     (egrep with negation)
      //     S        REG_SHELL               SRE     (sh glob)
      //     K        REG_SHELL|REG_AUGMENTED KRE     (ksh glob)
      //     L        REG_LITERAL             LRE     (fgrep)
      //     a        REG_LEFT|REG_RIGHT      implicit ^...$
      //     b        REG_NOTBOL              lhs does not match ^
      //     c        REG_COMMENT             ignore space and #...\n
      //     d        REG_SHELL_DOT           explicit leading . match
      //     e        REG_NOTEOL              rhs does not match $
      //     f        REG_MULTIPLE            multiple \n separated patterns
      //     g        FNM_LEADING_DIR         testfnmatch only -- match until /
      //     h        REG_MULTIREF            multiple digit backref
      //     i        REG_ICASE               ignore case
      //     j        REG_SPAN                . matches \n
      //     k        REG_ESCAPE              \ to ecape [...] delimiter
      //     l        REG_LEFT                implicit ^...
      //     m        REG_MINIMAL             minimal match
      //     n        REG_NEWLINE             explicit \n match
      //     o        REG_ENCLOSED            (|&) magic inside [@|&](...)
      //     p        REG_SHELL_PATH          explicit / match
      //     q        REG_DELIMITED           delimited pattern
      //     r        REG_RIGHT               implicit ...$
      //     s        REG_SHELL_ESCAPED       \ not special
      //     t        REG_MUSTDELIM           all delimiters must be specified
      //     u        standard unspecified behavior -- errors not counted
      //     v        REG_CLASS_ESCAPE        \ special inside [...]
      //     w        REG_NOSUB               no subexpression match array
      //     x        REG_LENIENT             let some errors slide
      //     y        REG_LEFT                regexec() implicit ^...
      //     z        REG_NULL                NULL subexpressions ok
      //     $                                expand C \c escapes in fields
      //                                      2 and 3
      //     /                                field 2 is a regsubcomp() expr
      //     =                                field 3 is a regdecomp() expr
      //   Field 1 control lines:
      //     C                set LC_COLLATE and LC_CTYPE to locale in field 2
      //     ?test ...        output field 5 if passed and != EXPECTED,
      //                      silent otherwise
      //     &test ...        output field 5 if current and previous passed
      //     |test ...        output field 5 if current passed and
      //                      previous failed
      //     ; ...            output field 2 if previous failed
      //     {test ...        skip if failed until }
      //     }                end of skip
      //     : comment        comment copied as output NOTE
      //     :comment:test    :comment: ignored
      //     N[OTE] comment   comment copied as output NOTE
      //     T[EST] comment   comment
      //     number           use number for nmatch (20 by default)
      var flag = field.get(0)
      flag.charAt(0) match {
        case '?' | '&' | '|' | ';' | '{' | '}' =>
          // Ignore all the control operators.
          // Just run everything.
          flag = flag.substring(1)
          if (flag.isEmpty) break
        case ':' =>
          val i = flag.indexOf(':', 1)
          if (i < 0) {
            System.err.format("skip: %s\n", line)
            break
          }
          flag = flag.substring(1 + i + 1)

        case 'C' | 'N' | 'T' | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' |
            '8' | '9' =>
          System.err.println("skip: %s\n".format(line))
          break
        case _ =>
      }
      // Can check field count now that we've handled the myriad comment
      // formats.
      if (field.size < 4) {
        System.err.println(
          "%s:%d: too few fields: %s\n".format(file, lineno, line))
        nerr += 1
        break
      }
      // Expand C escapes (a.k.a. Go escapes).
      if (flag.indexOf('$') >= 0) {
        var f = "\"" + field.get(1) + "\""
        try field.set(1, Strconv.unquote(f))
        catch {
          case NonFatal(e) =>
            System.err.println(
              "%s:%d: cannot unquote %s\n".format(file, lineno, f))
            nerr += 1
        }
        f = "\"" + field.get(2) + "\""
        try field.set(2, Strconv.unquote(f))
        catch {
          case NonFatal(e) =>
            System.err.println(
              "%s:%d: cannot unquote %s\n".format(file, lineno, f))
            nerr += 1
        }
      }
      //   Field 2: the regular expression pattern; SAME uses the pattern from
      //     the previous specification.
      if (field.get(1) == "SAME") field.set(1, lastRegexp)
      lastRegexp = field.get(1)
      //   Field 3: the string to match.
      val text = field.get(2)
      //   Field 4: the test outcome...
      val shouldCompileMatch = Array(false, false)
      // in/out param to parser
      var pos: util.List[Integer] = null
      try pos = parseFowlerResult(field.get(3), shouldCompileMatch)
      catch {
        case NonFatal(e) =>
          System.err.println(
            "%s:%d: cannot parse result %s\n"
              .format(file, lineno, field.get(3)))
          nerr += 1
          break
      }
      //   Field 5: optional comment appended to the report.
      // Run test once for each specified capital letter mode that we support.
      var _break = false
      for (c <- flag.toCharArray if !_break) {
        var pattern = field.get(1)
        var flags   = RE2.POSIX | RE2.CLASS_NL
        c match {
          case 'E' =>
            // extended regexp (what we support)
            _break = true
          case 'L' =>
            // literal
            pattern = RE2.quoteMeta(pattern)
          case _ =>
            break
        }
        if (!_break) {
          if (flag.indexOf('i') >= 0) flags |= RE2.FOLD_CASE
          var re: RE2 = null
          try re = RE2.compileImpl(pattern, flags, true)
          catch {
            case e: PatternSyntaxException =>
              if (shouldCompileMatch(0)) {
                System.err.println(
                  "%s:%d: %s did not compile\n"
                    .format(file, lineno, pattern))
                nerr += 1
              }
              break
          }
          if (!shouldCompileMatch(0)) {
            System.err.println(
              "%s:%d: %s should not compile\n"
                .format(file, lineno, pattern))
            nerr += 1
            break
          }
          val match0 = re.match_(text)
          if (match0 != shouldCompileMatch(1)) {
            System.err.println(
              "%s:%d: %s.match(%s) = %s, want %s\n"
                .format(file, lineno, pattern, text, match0, !match0))
            nerr += 1
            break
          }
          var haveArray = re.findSubmatchIndex(text)
          if (haveArray == null) haveArray = Utils.EMPTY_INTS // to make .length and printing safe
          if ((haveArray.length > 0) != match0) {
            System.err.println(
              "%s:%d: %s.match(%s) = %s, " + "but %s.findSubmatchIndex(%s) = %s\n"
                .format(file,
                        lineno,
                        pattern,
                        text,
                        match0,
                        pattern,
                        text,
                        util.Arrays.toString(haveArray)))
            nerr += 1
            break
          }
          // Convert int[] to List<Integer> and truncate to pos.length.
          val have = new util.ArrayList[Integer]
          var i    = 0
          while (i < pos.size) {
            have.add(haveArray(i))
            i += 1
          }
          if (!(have == pos)) {
            System.err.println(
              "%s:%d: %s.findSubmatchIndex(%s) = %s, want %s\n"
                .format(file, lineno, pattern, text, have, pos))
            nerr += 1
            break
          }
        }
      }
    }
    if (nerr > 0) fail("There were " + nerr + " errors")
  }

  private def parseFowlerResult(
      _s: String,
      shouldCompileMatch: Array[Boolean]): util.List[Integer] = {
    var s    = _s
    val olds = s
    //   Field 4: the test outcome. This is either one of the posix error
    //     codes (with REG_ omitted) or the match array, a list of (m,n)
    //     entries with m and n being first and last+1 positions in the
    //     field 3 string, or NULL if REG_NOSUB is in effect and success
    //     is expected. BADPAT is acceptable in place of any regcomp(3)
    //     error code. The match[] array is initialized to (-2,-2) before
    //     each test. All array elements from 0 to nmatch-1 must be specified
    //     in the outcome. Unspecified endpoints (offset -1) are denoted by ?.
    //     Unset endpoints (offset -2) are denoted by X. {x}(o:n) denotes a
    //     matched (?{...}) expression, where x is the text enclosed by {...},
    //     o is the expression ordinal counting from 1, and n is the length of
    //     the unmatched portion of the subject string. If x starts with a
    //     number then that is the return value of re_execf(), otherwise 0 is
    //     returned.
    if (s.isEmpty) { // Match with no position information.
      shouldCompileMatch(0) = true
      shouldCompileMatch(1) = true
      return Collections.emptyList[Integer]
    } else if (s == "NOMATCH") { // Match failure.
      shouldCompileMatch(0) = true
      shouldCompileMatch(1) = false
      return Collections.emptyList[Integer]
    } else if ('A' <= s.charAt(0) && s.charAt(0) <= 'Z') { // All the other error codes are compile errors.
      shouldCompileMatch(0) = false
      return Collections.emptyList[Integer]
    }
    shouldCompileMatch(0) = true
    shouldCompileMatch(1) = true
    val result = new util.ArrayList[Integer]
    while (!s.isEmpty) {
      var end = ')'
      if ((result.size % 2) == 0) {
        if (s.charAt(0) != '(')
          throw new RuntimeException("parse error: missing '('")
        s = s.substring(1)
        end = ','
      }
      val i = s.indexOf(end)
      if (i <= 0) { // [sic]
        throw new RuntimeException("parse error: missing '" + end + "'")
      }
      val num = s.substring(0, i)
      if (!(num == "?")) result.add(Integer.valueOf(num)) // (may throw)
      else result.add(-1)
      s = s.substring(i + 1)
    }
    if ((result.size % 2) != 0)
      throw new RuntimeException("parse error: odd number of fields")
    result
  }
}
