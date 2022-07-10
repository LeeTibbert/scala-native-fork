package scala.scalanative
package posix

import scala.scalanative.libc
import scala.scalanative.posix.sys.types
import scala.scalanative.unsafe._

@extern
object stddef {
  type ptrdiff_t = libc.stddef.ptrdiff_t
  type wchar_t = libc.stddef.ptrdiff_t
  type size_t = types.size_t

// Macros

  // Ptr[Byte] is Scala Native convention for C (void *).
  @name("scalanative_posix_null")
  def NULL: Ptr[Byte] = extern

  // offsetof() is not implemented in Scala Native.
}
