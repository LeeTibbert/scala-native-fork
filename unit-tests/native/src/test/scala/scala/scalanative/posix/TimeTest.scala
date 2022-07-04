package scala.scalanative.posix

import org.junit.Test
import org.junit.Assert._
import org.junit.Assume._

import java.io.IOException

import org.scalanative.testsuite.utils.Platform
import scala.scalanative.meta.LinktimeInfo.isWindows
import scala.scalanative.runtime.PlatformExt

import scalanative.libc.{errno => libcErrno, string}
import scala.scalanative.unsafe._
import scala.scalanative.unsigned._

import scala.scalanative.posix.errno.{EINVAL, EINTR}
import scala.scalanative.posix.signal
import scala.scalanative.posix.time._
import scala.scalanative.posix.timeOps.{timespecOps, tmOps}

class TimeTest {
  tzset()

  // Note: alloc clears memory

  // In 2.11/2.12 time was resolved to posix.time.type, in 2.13 to
  // posix.time.time method.
  val now_time: time_t = scala.scalanative.posix.time.time(null)
  val epoch: time_t = 0L

  @Test def asctimeWithGivenKnownStateShouldMatchItsRepresentation(): Unit =
    if (!isWindows) {
      Zone { implicit z =>
        val anno_zero_ptr = alloc[tm]()
        anno_zero_ptr.tm_mday = 1
        anno_zero_ptr.tm_wday = 1
        val cstr: CString = asctime(anno_zero_ptr)
        val str: String = fromCString(cstr)
        assertEquals("Mon Jan  1 00:00:00 1900\n", str)
      }
    }

  @Test def asctime_rWithGivenKnownStateShouldMatchItsRepresentation(): Unit =
    if (!isWindows) {
      Zone { implicit z =>
        val anno_zero_ptr = alloc[tm]()
        anno_zero_ptr.tm_mday = 1
        anno_zero_ptr.tm_wday = 1
        val cstr: CString = asctime_r(anno_zero_ptr, alloc[Byte](26))
        val str: String = fromCString(cstr)
        assertEquals("Mon Jan  1 00:00:00 1900\n", str)
      }
    }

  @Test def localtimeShouldHandleEpochPlusTimezone(): Unit =
    if (!isWindows) {
      assumeFalse(
        "Skipping localtime test since FreeBSD hasn't the 'timezone' variable",
        Platform.isFreeBSD
      )

      /* unix epoch is defined as 0 seconds UTC (Universal Time).
       * 'timezone' is defined in Posix as seconds WEST of UTC. Yes WEST.
       * At 'epoch + timezone seconds' it will be 0 seconds local time.
       * That local time should display as the expected "Thu Jan etc".
       *
       * The logic here is the inverse of what one would expect. This
       * is to avoid having to deal with daylight saving issues. We
       * know the standard timezone but the 'is_dst' field is documented
       * as unreliable.
       */

      val time_ptr = stackalloc[time_t]()
      !time_ptr = epoch + timezone()
      val time: Ptr[tm] = localtime(time_ptr)
      val cstr: CString = asctime(time)
      val str: String = fromCString(cstr)

      assertEquals("Thu Jan  1 00:00:00 1970\n", str)
    }

  @Test def localtime_rShouldHandleEpochPlusTimezone(): Unit =
    if (!isWindows) {
      Zone { implicit z =>
        assumeFalse(
          "Skipping localtime_r test since FreeBSD hasn't the 'timezone' variable",
          Platform.isFreeBSD
        )

        // See _essential_ comment in corresponding localtime test about logic.

        val time_ptr = stackalloc[time_t]()
        !time_ptr = epoch + timezone()
        val time: Ptr[tm] = localtime_r(time_ptr, alloc[tm]())
        val cstr: CString = asctime_r(time, alloc[Byte](26))
        val str: String = fromCString(cstr)

        assertEquals("Thu Jan  1 00:00:00 1970\n", str)
      }
    }

  @Test def difftimeBetweenEpochAndNowGreaterThanTimestampWhenCodeWasWritten()
      : Unit = {
    assertTrue(difftime(now_time, epoch) > 1502752688)
  }

  @Test def timeNowGreaterThanTimestampWhenCodeWasWritten(): Unit =
    if (!isWindows) {
      // arbitrary date set at the time when I was writing this.
      assertTrue(now_time > 1502752688)
    }

  @Test def strftimeDoesNotReadMemoryOutsideStructTm(): Unit =
    if (!isWindows) {
      Zone { implicit z =>
        // The purpose of this test is to check two closely related conditions.
        // These conditions not a concern when the size of the C structure
        // is the same as the Scala Native structure and the order of the
        // fields match. They are necessary on BSD or glibc derived systems
        // where the Operating System libc uses 56 bytes, where the "extra"
        // have a time-honored, specified meaning.
        //
        //   1) Did time.scala strftime() have "@name" to ensure that structure
        //      copy-in/copy-out happened? Failure case is if 36 byte
        //      Scala Native tm got passed as-is to C strftime on a BSD/glibc
        //      system.
        //
        //   2) Did time.c strftime() zero any "excess" bytes if the C structure
        //      is larger than the Scala Native one? Failure case is that the
        //      timezone name in the output fails to match the expected regex.
        //      Often the mismatch consists of invisible, non-printing
        //      characters.
        //
        // Review the logic of this test thoroughly if size of "tm" changes.
        // This test may no longer be needed or need updating.
        assertEquals(
          "Review test! sizeof[Scala Native struct tm] changed",
          sizeof[tm],
          36.toULong
        )

        val ttPtr = alloc[time_t]()
        !ttPtr = 1490986064740L / 1000L // Fri Mar 31 14:47:44 EDT 2017

        // This code is testing for reading past the end of a "short"
        // Scala Native tm, so the linux 56 byte form is necessary here.
        val tmBufCount = 7.toULong

        val tmBuf: Ptr[Ptr[Byte]] = alloc[Ptr[Byte]](tmBufCount)

        val tmPtr = tmBuf.asInstanceOf[Ptr[tm]]

        if (localtime_r(ttPtr, tmPtr) == null) {
          throw new IOException(fromCString(string.strerror(libcErrno.errno)))
        } else {
          val unexpected = "BOGUS"

          // With the "short" 36 byte SN struct tm tmBuf(6) is
          // BSD linux tm_zone, and outside the posix minimal required
          // range. strftime() should not read it.
          tmBuf(6) = toCString(unexpected)

          // grossly over-provision rather than chase fencepost bugs.
          val bufSize = 70.toULong
          val buf: Ptr[Byte] = alloc[Byte](bufSize)

          val n = strftime(buf, bufSize, c"%a %b %d %T %Z %Y", tmPtr)

          // strftime does not set errno on error
          assertNotEquals("unexpected zero from strftime", n, 0)

          val result = fromCString(buf)
          val len = "Fri Mar 31 14:47:44 ".length

          // time.scala @name caused structure copy-in/copy-out.
          assertEquals("strftime failed", result.indexOf(unexpected, len), -1)

          val regex = "[A-Z][a-z]{2} [A-Z][a-z]{2} " +
            "\\d\\d \\d{2}:\\d{2}:\\d{2} [A-Z]{2,5} 2017"

          // time.c strftime() zeroed excess bytes in BSD/glibc struct tm.
          assertTrue(
            s"result: '${result}' does not match regex: '${regex}'",
            result.matches(regex)
          )
        }
      }
    }

  @Test def strftimeForJanOne1900ZeroZulu(): Unit = if (!isWindows) {
    Zone { implicit z =>
      val isoDatePtr: Ptr[CChar] = alloc[CChar](70)
      val timePtr = alloc[tm]()

      timePtr.tm_mday = 1

      strftime(isoDatePtr, 70.toULong, c"%FT%TZ", timePtr)

      val isoDateString: String = fromCString(isoDatePtr)

      assertEquals("1900-01-01T00:00:00Z", isoDateString)
    }
  }

  @Test def strftimeForMondayJanOne1990ZeroTime(): Unit = if (!isWindows) {
    Zone { implicit z =>
      val timePtr = alloc[tm]()
      val datePtr: Ptr[CChar] = alloc[CChar](70)

      timePtr.tm_mday = 1
      timePtr.tm_wday = 1

      strftime(datePtr, 70.toULong, c"%A %c", timePtr)

      val dateString: String = fromCString(datePtr)
      assertEquals("Monday Mon Jan  1 00:00:00 1900", dateString)
    }
  }

  @Test def strptimeDetectsGrosslyInvalidFormat(): Unit = if (!isWindows) {
    Zone { implicit z =>
      val tmPtr = alloc[tm]()

      // As described in the Scala Native time.c implementation,
      // the format string is passed, unchecked, to the underlying
      // libc. All(?) will reject %Q in format.
      //
      // Gnu, macOS, and possibly other libc implementations parse
      // strftime specifiers such as %Z. As described in time.c, the
      // implementation under test is slightly non-conforming because
      // it does not reject specifiers accepted by the underlying libc.

      val result =
        strptime(c"December 31, 2016 23:59:60", c"%B %d, %Y %Q", tmPtr)

      assertTrue(s"expected null result, got pointer", result == null)
    }
  }

  @Test def strptimeDetectsInvalidString(): Unit = if (!isWindows) {
    Zone { implicit z =>
      val tmPtr = alloc[tm]()

      // 32 in string is invalid
      val result =
        strptime(c"December 32, 2016 23:59:60", c"%B %d, %Y %T", tmPtr)

      assertTrue(s"expected null result, got pointer", result == null)
    }
  }

  @Test def strptimeDetectsStringShorterThanFormat(): Unit = if (!isWindows) {
    Zone { implicit z =>
      val tmPtr = alloc[tm]()

      val result =
        strptime(c"December 32, 2016 23:59", c"%B %d, %Y %T", tmPtr)

      assertTrue(s"expected null result, got pointer", result == null)
    }
  }

  @Test def strptimeDoesNotWriteMemoryOutsideStructTm(): Unit =
    if (!isWindows) {
      Zone { implicit z =>
        // The purpose of this test is to check that time.scala method
        // declaration had an "@name" annotation, so that structure
        // copy-in/copy-out happened? Failure case is if 36 byte
        // Scala Native tm got passed as-is to C strptime on a BSD/glibc
        // or macOS system; see the tm_gmtoff & tm_zone handling below.

        // This is not a concern when the size of the C structure
        // is the same as the Scala Native structure and the order of the
        // fields match. They are necessary on BSD, glibc derived, macOS,
        // and possibly other systems where the Operating System libc
        // uses 56 bytes, where the "extra" have a time-honored, specified
        // meaning.
        //
        // Key to magic numbers 56 & 36.
        // Linux _BSD_Source and macOS use at least 56 Bytes.
        // Posix specifies 36 but allows more.

        // Review logic of this test thoroughly if size of "tm" changes.
        // This test may no longer be needed or need updating.
        assertEquals(
          "Review test! sizeof[Scala Native struct tm] changed",
          sizeof[tm],
          36.toULong
        )

        val tmBufSize = 56.toULong
        val tmBuf: Ptr[Byte] = alloc[Byte](tmBufSize)

        val tmPtr = tmBuf.asInstanceOf[Ptr[tm]]

        val gmtIndex = 36.toULong

        // To detect the case where SN strptime() is writing tm_gmtoff
        // use a value outside the known range of valid values.
        // This can happen if "@name" annotation has gone missing.

        val expectedGmtOff = Long.MaxValue
        (tmBuf + gmtIndex).asInstanceOf[Ptr[CLong]](0) = expectedGmtOff

        // %Z is not a supported posix conversion specification, but
        // is useful here to detect a defect in the method-under-test.

        val cp =
          strptime(c"Fri Mar 31 14:47:44 2017", c"%a %b %d %T %Y", tmPtr)

        assertNotNull(s"strptime returned unexpected null", cp)

        val ch = cp(0) // last character not processed by strptime().
        assertEquals("strptime() result is not NUL terminated", ch, '\u0000')

        // tm_gmtoff & tm_zone are outside the posix defined range.
        // Scala Native strftime() should never write to them.
        //
        // Assume no leading or interior padding.

        val tm_gmtoff = (tmBuf + gmtIndex).asInstanceOf[Ptr[CLong]](0)
        assertEquals("tm_gmtoff", expectedGmtOff, tm_gmtoff)

        val tmZoneIndex = (gmtIndex + sizeof[CLong])
        val tm_zone = (tmBuf + tmZoneIndex).asInstanceOf[CString]
        assertNull("tm_zone", null)

        // Major concerning conditions passed. Consistency check the tm proper.

        val expectedSec = 44
        assertEquals("tm_sec", expectedSec, tmPtr.tm_sec)

        val expectedMin = 47
        assertEquals("tm_min", expectedMin, tmPtr.tm_min)

        val expectedHour = 14
        assertEquals("tm_hour", expectedHour, tmPtr.tm_hour)

        val expectedMday = 31
        assertEquals("tm_mday", expectedMday, tmPtr.tm_mday)

        val expectedMonth = 2
        assertEquals("tm_mon", expectedMonth, tmPtr.tm_mon)

        val expectedYear = 117
        assertEquals("tm_year", expectedYear, tmPtr.tm_year)

        val expectedWday = 5
        assertEquals("tm_wday", expectedWday, tmPtr.tm_wday)

        val expectedYday = 89
        assertEquals("tm_yday", expectedYday, tmPtr.tm_yday)

        // Per posix specification, contents of tm_isdst are not reliable.
      }
    }

  @Test def strptimeFor31December2016Time235960(): Unit = if (!isWindows) {
    Zone { implicit z =>
      val tmPtr = alloc[tm]()

      // A leap second was added at this time
      val result =
        strptime(c"December 31, 2016 23:59:60", c"%B %d, %Y %T", tmPtr)

      assertNotEquals(
        "unexpected null return from strptime() call",
        null,
        result
      )

      val expectedYear = 116
      assertEquals("tm_year", expectedYear, tmPtr.tm_year)

      val expectedMonth = 11
      assertTrue(
        s"tm_mon: ${tmPtr.tm_mon} != expected: ${expectedMonth}",
        tmPtr.tm_mon == expectedMonth
      )

      val expectedMday = 31
      assertEquals("tm_mday", expectedMday, tmPtr.tm_mday)

      val expectedHour = 23
      assertEquals("tm_hour", expectedHour, tmPtr.tm_hour)

      val expectedMin = 59
      assertEquals("tm_min", expectedMin, tmPtr.tm_min)

      val expectedSec = 60
      assertEquals("tm_sec", expectedSec, tmPtr.tm_sec)

    // Per posix specification, contents of tm_isdst are not reliable.
    }
  }

  @Test def strptimeExtraTextAfterDateStringIsOK(): Unit = if (!isWindows) {
    Zone { implicit z =>
      val tmPtr = alloc[tm]()

      val result =
        strptime(c"December 31, 2016 23:59:60 UTC", c"%B %d, %Y %T ", tmPtr)

      assertTrue(s"error: null returned", result != null)

      val expected = 'U'
      assertTrue(
        s"character: ${!result} != expected: ${expected}",
        !result == expected
      )
    }
  }

  @Test def clockGetresReturnsBelievableResults(): Unit = if (!isWindows) {
    val timespecP = stackalloc[timespec]()
    timespecP.tv_sec = Long.MinValue // initialize with known bad values
    timespecP.tv_nsec = Long.MinValue

    val result = clock_getres(CLOCK_REALTIME, timespecP)

    assertEquals(
      s"clock_getres failed with errno: ${libcErrno.errno}",
      0,
      result
    )

    assertEquals(
      s"clock_getres tv_sec ${timespecP.tv_sec} != 0",
      0,
      timespecP.tv_sec
    )

    // Apparently silly test ensures CLOCKS_PER_SEC is exercised.
    assertTrue(
      s"clock_getres tv_nsec ${timespecP.tv_nsec} not in interval" +
        s" [0, ${CLOCKS_PER_SEC})",
      (timespecP.tv_nsec > 0) && (timespecP.tv_nsec <= CLOCKS_PER_SEC)
    )

    assertTrue(
      s"clock_getres tv_nsec ${timespecP.tv_nsec} is greater than millisecond",
      timespecP.tv_nsec <= (1 * 1000 * 1000)
    )

  }

  @Test def clockGettimeReturnsBelievableResults(): Unit = if (!isWindows) {
    val timespecP = stackalloc[timespec]()
    timespecP.tv_nsec = Long.MinValue // initialize with known bad value

    val now = time(null) // Seconds since Epoch

    val result = clock_gettime(CLOCK_REALTIME, timespecP)

    assertEquals(
      s"clock_gettime failed with errno: ${libcErrno.errno}",
      0,
      result
    )

    /* The two time fetches were not done as one atomic transaction so
     * the times can and do validly vary by a "small" amount.
     *
     * Leap seconds, double leap seconds, process scheduling, VM machine
     * swapouts, and a number of factors can cause the difference.
     *
     * The challenge of defining "small" becomes an exercise in balancing
     * the reporting of false positives vs false negatives, the concept of
     * "Receiver Operating Characteristics". False positives in CI waste
     * a __lot__ of time, so err on the high side.
     *
     * Normally, the two times would be withing microseconds of each other,
     * well less than a second. Leap seconds, double leap seconds can add
     * a second or more, slow machines, etc.
     * 5 is a generous guess. Lets see if time proves it a good trade off.
     * The basic idea is to detect wildly wrong results from the unit under
     * test, not to stress either race conditions or developers.
     */

    val acceptableDiff = 5L
    val secondsDiff = Math.abs(timespecP.tv_sec - now)

    assertTrue(
      s"clock_gettime seconds ${secondsDiff} not within ${acceptableDiff}",
      secondsDiff <= acceptableDiff
    )

    assertTrue(
      s"clock_gettime nanoseconds ${timespecP.tv_nsec} not in " +
        s"interval [0, 999999999]",
      (timespecP.tv_nsec >= 0L) && (timespecP.tv_nsec <= 999999999L)
    )
  }

  @Test def clockNanosleepShouldExecute(): Unit = if (!isWindows) {
    val requestP = stackalloc[timespec]()
    requestP.tv_sec = 0L
    requestP.tv_nsec = 1L // will be rounded up to minimum clock resolution.

    val result = clock_nanosleep(CLOCK_MONOTONIC, flags = 0, requestP, null)

    if (result == 0) {
      /* Full sleep should have happened.
       * Hard to test/verify. Nanosecond delays,
       * even rounded up to clock granularity, are exceedingly small
       * compared to background of OS & hardware, especialy VM, noise.
       */
    } else if (libcErrno.errno == EINTR) {
      // EINTR means sleep was interrupted, clock_nanosleep() executed.
    } else if (Platform.isMacOs) {
      // No clock_nanosleep() on macOS. stub in time.c always return EINVAL.
      assertEquals(
        s"clock_nanosleep unexpected macOS errno: ${libcErrno.errno}",
        EINVAL,
        libcErrno.errno
      )
    } else {
      assertTrue(
        s"clock_nanosleep failed with errno: ${libcErrno.errno}",
        false
      )
    }
  }

  @Test def clockSettimeShouldExecute(): Unit = if (!isWindows) {
    val timespecP = stackalloc[timespec]()

    // CLOCK_MONOTONIC is defined as un-settable, use to cause error result.
    val result = clock_settime(CLOCK_MONOTONIC, timespecP)

    assertEquals(
      s"clock_settime should have failed setting CLOCK_MONOTONIC",
      -1,
      result
    )

    assertEquals(
      s"clock_settime failed with errno: ${libcErrno.errno}",
      EINVAL,
      libcErrno.errno
    )
  }

  private def checkMacOsTimerResults(
      label: String,
      status: CInt,
      errno: CInt
  ): Unit = {

    assertEquals(
      s"macOS '${label}' returned unexpected status",
      -1,
      status
    )

    assertEquals(
      s"macOS '${label}' returned unexpected errno",
      EINVAL,
      errno
    )
  }

  /* There is no need to link with "-lrt" here.
   * One would need to supply that option to exercise methods on Unix.
   *
   * This Test does two things.  First shows that the macOS stubs are working.
   * Second, it shows that arguments, "@name" etc. are working and should
   * work on Unix, if linked with "-lrt".
   *
   * Unix tests are not provided because they involve both supplying a
   * special link option and in generating and handling signals.
   * If/When the need develops, such tests could be done in a separate file.
   */

  @Test def allMacOsTimersReturnMinusOne(): Unit = if (!isWindows) {
    if (Platform.isMacOs) {
      Zone { implicit z =>
        locally {
          val sevp = stackalloc[signal.sigevent]()
          val timeridP = stackalloc[timer_t]()

          val result = timer_create(CLOCK_MONOTONIC, sevp, timeridP)
          checkMacOsTimerResults("timer_create", result, libcErrno.errno)
        }

        locally {
          // call with intended bogus timerid
          val result = timer_delete(null.asInstanceOf[timer_t])
          checkMacOsTimerResults("timer_delete", result, libcErrno.errno)
        }

        locally {
          // call with intended bogus timerid
          val result = timer_getoverrun(null.asInstanceOf[timer_t])
          checkMacOsTimerResults("timer_getoverrun", result, libcErrno.errno)
        }

        locally {
          val curr_value = stackalloc[itimerspec]()

          // call with intended bogus timerid
          val result = timer_gettime(null.asInstanceOf[timer_t], curr_value)
          checkMacOsTimerResults("timer_gettime", result, libcErrno.errno)
        }

        locally {
          val new_value = stackalloc[itimerspec]()
          val old_value = stackalloc[itimerspec]()

          // call with intended bogus timerid
          val result = timer_settime(
            null.asInstanceOf[timer_t],
            flags = TIMER_ABSTIME,
            new_value,
            old_value
          )
          checkMacOsTimerResults("timer_settime", result, libcErrno.errno)
        }
      } // Zone
    } // Platform.isMacOs
  }
}
