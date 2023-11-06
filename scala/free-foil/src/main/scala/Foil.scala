import Foil.{DistinctEvidence, ExtEvidence}

import scala.collection.immutable.IntMap
import scala.language.implicitConversions

object Foil extends  App{
  sealed trait Expr[+N]
  case class Var[N <: S](name: Name[N]) extends Expr[N]
  case class Lam[N <: S, L <: S](lamExpr: LamExpr[N, L]) extends Expr[N]
  case class App[N <: S](expr1: Expr[N], expr2: Expr[N]) extends Expr[N]
  case class LamExpr[N <: S, L <: S](nameBinder: NameBinder[N, L], expr: Expr[L])

  case class RawName(rawId: Int)

  case class RawScope(rawSet: Set[Int])

  val rawEmptyScope: RawScope = RawScope(Set.empty[Int])

  def rawFreshName(rawScope: RawScope): RawName = rawScope match {
    case RawScope(s) if s.isEmpty => RawName(0)
    case RawScope(s) => RawName(s.max + 1)
  }

  def rawExtendScope(rawName: RawName, rawScope: RawScope): RawScope =
    RawScope(rawScope.rawSet + rawName.rawId)

  def rawMember(rawName: RawName)(rawScope: RawScope): Boolean =
    rawScope.rawSet.contains(rawName.rawId)

  case class RawSubst[A](rawMap: IntMap[A])

  def rawIdSubst[A] = IntMap.empty[A]

  def rawLookup[A](rawSubst: RawSubst[A])(rawName: RawName): Option[A] =
    rawSubst.rawMap.get(rawName.rawId)

  def rawExtendSubst[A](rawName: RawName, value: A, rawSubst: RawSubst[A]): RawSubst[A] =
    RawSubst(rawSubst.rawMap.updated(rawName.rawId, value))



  sealed trait S
  case class VoidS() extends S

  case class Name[N <: S](unsafeName: RawName)
  case class Scope[N <: S](unsafeScope: RawScope)

  val emptyScope = Scope[VoidS](rawEmptyScope)

  def member[L <: S, N <: S](name: Name[L])(scope: Scope[N]): Boolean =
    rawMember(name.unsafeName)(scope.unsafeScope)



  case class NameBinder[N <: S, L <: S](unsafeBinder: Name[L])

  def nameOf[N <: S, L <: S](nameBinder: NameBinder[N, L]): Name[L] =
    nameBinder.unsafeBinder

  def extendScope[N <: S, L <: S](nameBinder: NameBinder[N, L], scope: Scope[N]): Scope[L] =
    Scope[L](rawExtendScope(nameBinder.unsafeBinder.unsafeName, scope.unsafeScope))

  def withFreshBinder[N <: S, R](scope: Scope[N])(cont: [L] => NameBinder[N, L] => R): R =
    cont(NameBinder(Name(rawFreshName(scope.unsafeScope))))

  trait Ext[N, L]
  trait Distinct[N <: S]

  type DExt[N, L <: S] = (Distinct[L], Ext[N, L])

  sealed trait DistinctEvidence[N <: S]
  case class DistinctConstruct[N <: S](distinct: Distinct[N]) extends DistinctEvidence[N]

  sealed trait ExtEvidence[N <: S, L <: S]
  case class ExtConstruct[N <: S, L <: S](ext: Ext[N, L]) extends ExtEvidence[N, L]

  def unsafeDistinct[N <: S]: DistinctEvidence[N] =
    DistinctConstruct[VoidS].asInstanceOf[DistinctEvidence[N]]

  def unsafeExt[N <: S, L <: S]: ExtEvidence[N, L] =
    ExtConstruct[VoidS, VoidS].asInstanceOf[ExtEvidence[N, L]]

  trait Sinkable[E[_]] {
    def sinkabilityProof[N <: S, L <: S](rename: Name[N] => Name[L]): E[N] => E[L]
  }

  implicit object NameIsSinkable extends Sinkable[Name] {
    def sinkabilityProof[N <: S, L <: S](rename: Name[N] => Name[L]): Name[N] => Name[L] =
      unsafeName => Name(rename(unsafeName).unsafeName)
  }

  def sink[E[_]: Sinkable, N, L](en: E[N])(implicit ev: DExt[L, N]): E[L] = en.asInstanceOf[E[L]]

  def withFresh[N : Distinct, R](scope: Scope[N])(cont: [L] => DExt[N, L] ?=> NameBinder[N, L] => R): R =
    withFreshBinder[N, R](scope){(binder: NameBinder[N, _]) => unsafeAssertFresh(binder)(cont)}


  def unsafeAssertFresh[N,L,R](binder: NameBinder[_, _])(cont: DExt[N, L] ?=>  NameBinder[N, L] => R) = ???

  def withRefreshed[O: Distinct, I <: S, R](scope: Scope[O], name: Name[I])(cont: [O_] => DExt[O, O_] ?=> NameBinder[O, O_] => R): R =
    if (member[I, O](name)(scope)) withFresh(scope)(cont)
    else unsafeAssertFresh(NameBinder[O, I](name))(cont[O])

  case class Substitution[E[_], I <: S, O <: S](f: [N <: S] => Name[N] => E[N], env: IntMap[E[O]])

  def lookupSubst[E[_], I <: S, O <: S](subst: Substitution[E, I, O], name: Name[I]): E[O] =
    subst.env.get(name.unsafeName.rawId) match {
      case Some(e) => e
      case None => subst.f(Name(RawName(name.unsafeName.rawId)))
    }

  def idSubst[E[_], I <: S](f: [N <: S] => Name[N] => E[N]): Substitution[E, I, I] =
    Substitution(f, IntMap.empty)

  def addSubst[E[_], I <: S, O <: S, IPrime <: S](s: Substitution[E, I, O])(
    b: NameBinder[I, IPrime])(e: E[O]): Substitution[E, IPrime, O] = s match {
    case Substitution(f, env) => Substitution(f, env)
  }

  def addRename[E[_], I <: S, O <: S](s: Substitution[E, I, O])(
    b: NameBinder[I, I], n: Name[O]): Substitution[E, I, O] = s match {
    case Substitution(f, env) =>
      val name1 = b.unsafeBinder.unsafeName
      val name2 = n.unsafeName
      if (name1 == name2) s
      else addSubst(s)(b)(f(n))
  }

//  def substituteExpr[O <: S, I](scope: Scope[O], subst: Substitution[Expr, I, O])(expr: Expr[I])(implicit ev: Distinct[O]): Expr[O] = expr match {
//    case variable: Var[I] => lookupSubst[Expr, I, O](subst, variable.name)
//    case app: App[I] => App(substituteExpr(scope, subst)(app.expr1), substituteExpr(scope, subst)(app.expr2))
//    case lam: Lam[I, I] =>
//
//      val binder_ = withRefreshed(scope, lam.lamExpr.nameBinder.unsafeBinder){binder =>
//        val subst_ = addRename[Expr, I, O](subst)(binder, nameOf(binder)) // add sink
//        val scope_ = extendScope(binder, scope)
//        val body_ = substituteExpr(scope_, subst_)(lam.lamExpr.expr)
//        Lam[O, O](LamExpr(binder, body_))
//      }
//      binder_
//  }

}
