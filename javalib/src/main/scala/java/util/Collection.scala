// Ported from Scala.js commit: f122aa5 dated: 2019-07-03

package java.util

import java.util.function.Predicate

import scala.scalanative.annotation.JavaDefaultMethod

trait Collection[E] extends java.lang.Iterable[E] {
  def size(): Int
  def isEmpty(): Boolean
  def contains(o: Any): Boolean
  def iterator(): Iterator[E]
  def toArray(): Array[AnyRef]
  def toArray[T <: AnyRef](a: Array[T]): Array[T]
  def add(e: E): Boolean
  def remove(o: Any): Boolean
  def containsAll(c: Collection[_]): Boolean
  def addAll(c: Collection[_ <: E]): Boolean
  def removeAll(c: Collection[_]): Boolean

  @JavaDefaultMethod
  def removeIf(filter: Predicate[_ >: E]): Boolean = {
    var result = false
    val iter = iterator()
    while (iter.hasNext()) {
      if (filter.test(iter.next())) {
        iter.remove()
        result = true
      }
    }
    result
  }

  def retainAll(c: Collection[_]): Boolean
  def clear(): Unit
  def equals(o: Any): Boolean
  def hashCode(): Int
}
