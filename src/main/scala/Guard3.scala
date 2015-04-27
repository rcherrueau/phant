package phant

import scalaz._, StateT._
import shapeless._, Nat._

object Guard3 {
  type Idx = Int
  type DB[X] = List[X]
  type Guard3[S1,S2,A] = IndexedState[S1,S2,A]

  def configure[C1,C2,C3]: Guard3[Site0[DB[(Raw[C1],Raw[C2],Raw[C3])]],
                                  Site0[DB[(Raw[C1],Raw[C2],Raw[C3])]],
                                  Unit] =
    State(s => (s, ()))

  def crypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R2[C2] <: Rsc,
            R3[C3] <: Rsc,
            PT[C1] <: Protected](
    n: _1)(
    f: R1[C1] => PT[C1]): Guard3[S[DB[(R1[C1], R2[C2], R3[C3])]],
                                 S[DB[(PT[C1], R2[C2], R3[C3])]],
                                 Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (f(c1), c2, c3) }))


  def crypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R2[C2] <: Rsc,
            R3[C3] <: Rsc,
            PT[C2] <: Protected](
    n: _2)(
    f: R2[C2] => PT[C2]): Guard3[S[DB[(R1[C1], R2[C2], R3[C3])]],
                                 S[DB[(R1[C1], PT[C2], R3[C3])]],
                                 Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, f(c2), c3) }))

  def crypt[C1,C2,C3,
            S[X] <: Site[X,S],
            R1[C1] <: Rsc,
            R2[C2] <: Rsc,
            R3[C3] <: Rsc,
            PT[C3] <: Protected](
    n: _3)(
    f: R3[C3] => PT[C3]): Guard3[S[DB[(R1[C1], R2[C2], R3[C3])]],
                                 S[DB[(R1[C1], R2[C2], PT[C3])]],
                                 Unit] =
    State.iModify(s => s(s.get map { case (c1, c2, c3) => (c1, c2, f(c3)) }))

  def fragV[C1,C2,C3,
            S1[X] <: Site[X,S1],
            S2[X] <: Site[X,S2]](
    n: _1)(
    s1: S1[_],
    s2: S2[_]): Guard3[Site0[DB[(C1, C2, C3)]],
                       (S1[DB[(C1, Idx)]], S2[DB[(C2, C3, Idx)]]),
                       Unit] =
    State.iModify(s => {
                    val (lf, rf) = s.get.unzip(r => ((r._1), (r._2, r._3)))
                    (s1(lf.zipWithIndex), s2(rf.foldLeft((Nil:DB[(C2,C3,Idx)], 0)) {
                                               case ((db, i), (c2, c3)) =>
                                                 ((c2, c3, i) :: db, i + 1)
                                             }._1))
                  })

  def fragV[C1,C2,C3,
            S1[X] <: Site[X,S1],
            S2[X] <: Site[X,S2]](
    n: _2)(
    s1: S1[_],
    s2: S2[_]): Guard3[Site0[DB[(C1, C2, C3)]],
                       (S1[DB[(C1, C2, Idx)]], S2[DB[(C3, Idx)]]),
                       Unit] =
    State.iModify(s => {
                    val (lf, rf) = s.get.unzip(r => ((r._1, r._2), (r._3)))
                    (s1(lf.foldLeft((Nil:DB[(C1,C2,Idx)], 0)) {
                          case ((db, i), (c1, c2)) =>
                            ((c1, c2, i) :: db, i + 1)
                        }._1), s2(rf.zipWithIndex))
                  })

  def defragV[C1,C2,C3,
              S1[X] <: Site[X,S1],
              S2[X] <: Site[X,S2]](
    n: _1): Guard3[(S1[DB[(C1, Idx)]], S2[DB[(C2, C3, Idx)]]),
                   Site0[DB[(C1,C2,C3)]],
                   Unit] =
    State.iModify(s => {
                    val (lf, rf) = s
                    Site0(for {
                            (c1, i) <- lf.get
                            (c2, c3, j) <- rf.get
                            if (i == j)
                          } yield (c1, c2, c3))
                  })

  def defragV[C1,C2,C3,
              S1[X] <: Site[X,S1],
              S2[X] <: Site[X,S2]](
    n: _2): Guard3[(S1[DB[(C1, C2, Idx)]], S2[DB[(C3, Idx)]]),
                   Site0[DB[(C1,C2,C3)]],
                   Unit] =
    State.iModify(s => {
                    val (lf, rf) = s
                    Site0(for {
                            (c1, c2, i) <- lf.get
                            (c3, j) <- rf.get
                            if (i == j)
                          } yield (c1, c2, c3))
                  })

  def query[X,Q,
            S[X] <: Site[X,S]](q: X => Q): Guard3[S[X], S[X], S[Q]] =
    State.gets(s => s(q(s.get)))

  def queryL[X,Q,SR,
             SL[X] <: Site[X,SL]](q: X => Q): Guard3[(SL[X], SR),
                                                     (SL[X], SR),
                                                     SL[Q]] =
    State.gets({ case (sl, _) => sl(q(sl.get)) })

  def queryR[X,Q,SL,
             SR[X] <: Site[X,SR]](q: X => Q): Guard3[(SL, SR[X]),
                                                     (SL, SR[X]),
                                                     SR[Q]] =
    State.gets({ case (_, sr) => sr(q(sr.get)) })
}
