// Some miscellaneous useful definitions.

package notjs.util

import scala.runtime.ScalaRunTime

// the Scala compiler is not yet smart enough to figure out that it
// only needs to hash immutable objects once; extending case classes
// with this trait will make that happen. this one optimization can
// improve performance by orders of magnitude.
trait SmartHash extends Product {
  private lazy val cached = ScalaRunTime._hashCode(this)
  override def hashCode() = cached
}
