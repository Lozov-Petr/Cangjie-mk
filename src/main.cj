package test

import std.collection.{LinkedList
    // HashMap,
}

type VarIndex = Int

type Name = String

public enum List<T> {
    | Nil
    | Cons(T, List<T>)

    public static func toStringNoBrackets<T>(l: List<T>, sep!: String = " "): String where T <: ToString {
        match (l) {
            case Nil => ""
            case Cons(hd, Nil) => "${hd}"
            case Cons(hd, tl) => "${hd},${sep}${toStringNoBrackets(tl)}"
        }
    }

    public static func toStringNoBrackets<T1, T2>(l: List<(T1, T2)>, sep!: String = " "): String where T1 <: ToString,
        T2 <: ToString {
        match (l) {
            case Nil => ""
            case Cons((a, b), Nil) => "(${a}, ${b})"
            case Cons((a, b), tl) => "(${a}, ${b}),${sep}${toStringNoBrackets(tl)}"
            case Cons(_, _) => throw Exception("Unreachable case of toStringNoBrackets")
        }
    }

    public static func toString<T>(l: List<T>): String where T <: ToString {
        "[${toStringNoBrackets(l)}]"
    }

    public static func toString<T1, T2>(l: List<(T1, T2)>): String where T1 <: ToString, T2 <: ToString {
        "[${toStringNoBrackets(l)}]"
    }

    public static func foldLeft<Acc, E>(f: (Acc, E) -> Acc, acc: Acc, l: List<E>): Acc {
        match (l) {
            case Nil => acc
            case Cons(hd, tl) => foldLeft(f, f(acc, hd), tl)
        }
    }

    public static func find<K, V>(list: List<(K, V)>, key: K): Option<V> where K <: Equal<K> {
        match (list) {
            case Nil => None
            case Cons((a, b), tl) =>
                if (a == key) {
                    Some(b)
                } else {
                    find(tl, key)
                }
        }
    }
}

public enum Term <: ToString {
    | Var(VarIndex)
    | Ctor(Name, List<Term>)

    public func toString() {
        match (this) {
            case Var(i) => "_.${i}"
            case Ctor(name, args) => "${name} (${List<Any>.toStringNoBrackets(args)})"
        }
    }
}

type Substitution = List<(VarIndex, Term)>

extend Substitution {
    func ToString() {
        List.toString<VarIndex, Term>(this)
    }
}

public class Subst {
    public static func empty() {
        Nil<(VarIndex, Term)>
    }

    public static func add(varIndex: VarIndex, term: Term, subst: Substitution): Substitution {
        Cons((varIndex, term), subst)
    }

    private static func walk(term: Term, subst: Substitution): Term {
        match (term) {
            case Ctor(_, _) => term
            case Var(v) => match (List<Any>.find<VarIndex, Term>(subst, v)) {
                case None => term
                case Some(t) => t
            }
        }
    }

    private static func occursCheck(varIndex: VarIndex, term: Term, subst: Substitution): Bool {
        match (walk(term, subst)) {
            case Var(i) => i == varIndex
            case Ctor(_, args) => List<Any>.foldLeft({acc, e => acc || occursCheck(varIndex, e, subst)}, false, args)
        }
    }

    private static func extendSubst(varIndex: VarIndex, term: Term, subst: Substitution): Option<Substitution> {
        if (occursCheck(varIndex, term, subst)) {
            None
        } else {
            Some(add(varIndex, term, subst))
        }
    }

    private static func unifyArgs(args1: List<Term>, args2: List<Term>, subst: Substitution): Option<Substitution> {
        match ((args1, args2)) {
            case (Nil, Nil) => Some(subst)
            case (Cons(arg1, tl1), Cons(arg2, tl2)) => match (unify(arg1, arg2, subst)) {
                case None => None
                case Some(subst) => unifyArgs(tl1, tl2, subst)
            }
            case _ => throw Exception("Different amount of unified constructor arguments")
        }
    }

    public static func unify(t1: Term, t2: Term, subst: Substitution): Option<Substitution> {
        let walkedT2: Term = walk(t2, subst)
        match ((walk(t1, subst), walkedT2)) {
            case (Var(i), Var(j)) =>
                if (i == j) {
                    Some(subst)
                } else {
                    extendSubst(i, walkedT2, subst)
                }
            case (Var(i), walkedT2) => extendSubst(i, walkedT2, subst)
            case (walkedT1, Var(j)) => extendSubst(j, walkedT1, subst)
            case (Ctor(n1, args1), Ctor(n2, args2)) =>
                if (n1 == n2) {
                    unifyArgs(args1, args2, subst)
                } else {
                    None
                }
        }
    }
}

class StdTerms {
    static prop O: Term {
        get() {
            Ctor("O", List.Nil)
        }
    }

    static func S(n: Term): Term {
        Ctor("S", List.Cons(n, List.Nil))
    }

    static prop Nil: Term {
        get() {
            Ctor("Nil", List.Nil)
        }
    }

    static func Cons(hd: Term, tl: Term): Term {
        Ctor("Cons", List.Cons(hd, List.Cons(tl, List.Nil)))
    }

    static func Array2Term(array: Array<Term>): Term {
        var answer = Nil
        let range = (array.size - 1)..=0 : -1

        for (index in range) {
            answer = Cons(array[index], answer)
        }

        answer
    }

    static func Int2Term(n: Int): Term {
        if (n <= 0) {
            O
        } else {
            S(Int2Term(n - 1))
        }
    }

    static func mkConst(name: String): Term {
        Ctor(name, List.Nil)
    }
}

type State = (Substitution, VarIndex)

enum Stream {
    | Nil
    | Cons(State, Stream)
    | Thunk(() -> Stream)

    func force(): Stream {
        match (this) {
            case Thunk(f) => f()
            case _ => this
        }
    }

    func take(n: Int): LinkedList<Substitution> {
        let result = LinkedList<Substitution>()
        var self = this
        var counter = n

        while (counter > 0) {
            match (self.force()) {
                case Nil => break
                case Cons((st, _), xs) =>
                    result.append(st)
                    self = xs
                    counter--
                case Thunk(f) => self = self.force()
            }
        }

        result
    }

    func takeList(n: Int): List<Substitution> {
        match (n) {
            case 0 => List.Nil
            case _ => match (this) {
                case Nil => List.Nil
                case Cons((subst, _), xs) => List.Cons(subst, xs.takeList(n - 1))
                case Thunk(f) => f().takeList(n)
            }
        }
    }

    // static func delay(f: () -> Goal): Goal {
    //   { st => Thunk({ => f()(st) }) }
    // }

    static func unify(t1: Term, t2: Term): Goal {
        Goal {
            state: State =>
            let (subst, counter) = state
            match (Subst.unify(t1, t2, subst)) {
                case None => Nil
                case Some(s) => Cons((s, counter), Nil)
            }
        }
    }

    static func callFresh(f: (Term) -> Goal): Goal {
        Goal {
            state =>
            let (subst, counter) = state
            f(Var(counter)).g((subst, counter + 1))
        }
    }

    static func delay(g: () -> Goal): Goal {
        Goal {st => Thunk {=> g().g(st)}}
    }

    // static func disj(g1: Goal, g2: Goal): Goal {
    //   { state =>
    //     g1(state).mplus(g2(state))
    //   }
    // }

    // static func conj(g1: Goal, g2: Goal): Goal {
    //   { state =>
    //     g1(state).bind(g2)
    //   }
    // }

    static func run(n: Int, g: Goal): LinkedList<Substitution> {
        g.g((Subst.empty(), 0)).take(n)
    }

    func mplus(other: Stream): Stream {
        match (this) {
            case Nil => other.force()
            case Cons(x, xs) => Cons(x, Thunk({=> other.force().mplus(xs)}))
            case Thunk(_) => Thunk({=> other.force().mplus(this)})
        }
    }
    public func bind(g: (State) -> Stream): Stream {
        match (this) {
            case Nil => Nil
            case Cons(x, xs) => g(x).mplus(Thunk({=> xs.force().bind(g)}))
            case Thunk(f) => Thunk({=> f().bind(g)})
        }
    }
}

class Goal {
    var g: (State) -> Stream
    Goal(goal: (State) -> Stream) {
        g = goal
    }

    operator func &(a: Goal): Goal {
        return Goal {st => this.g(st).bind(a.g)}
    }
    operator func |(other: Goal): Goal {
        return Goal {st: State => this.g(st).mplus(other.g(st))}
    }

    public static func conde(arr: Array<Goal>): Goal {
        if (arr.size == 0) {
            return failure()
        } else {
            var acc = failure()
            for (g in arr) {
                acc = acc | g
            }
            return acc;
        }
    }

    public static func failure(): Goal {
        Goal {_ => Nil}
    }

    public static func success(): Goal {
        Goal {s => Cons(s, Stream.Nil)}
    }
}

func appendo(x: Term, y: Term, xy: Term): Goal {
    Goal.conde(
        Stream.unify(x, StdTerms.Nil) & Stream.unify(y, xy),
        Stream.callFresh(
            {
                hd: Term => Stream.callFresh(
                    {
                        xs: Term => Stream.callFresh(
                            {
                                xys: Term => Stream.unify(x, StdTerms.Cons(hd, xs)) &  Stream.unify(xy,
                                    StdTerms.Cons(hd, xys)) //& Stream.delay{ =>  appendo(xs, y, xys) }
                            })
                    })
            })
    )
}

// @Test
// public class TestA {
//   @TestCase 
//   func addTest() {
//     assertEqual(1,1)
//   }
// }

func ctor(name: String, args: Array<Term>): Term {
    if (args.size == 0) {
        return Ctor(name, List.Nil)
    }
    var acc = List<Term>.Nil;
    var i = args.size;
    while (i > 0) {
        i--;
        acc = List.Cons(args[i], acc)
    }
    return Ctor(name, acc)
}

main(): Int64 {
    // let l1: List<Int> = Nil
    // let l2 = Cons(1, l1)
    // let l3 = Cons(2, l2)
    // let l4 = Cons(3, l2)
    // println("hello world ${l3} | ${l4}")

    // println("${"a" == "a"}")
    // println("${"a" == "b"}")
    // let l = LinkedList<Int>()
    // let x1 = l.append(1)
    // let x2 = l.append(2)

    // println("hello world ${l}")

    // let t1 = Ctor("a", Cons(Ctor("b", Nil), Nil))
    // let t2 = Ctor("a", Cons(Var(0), Cons(Var(0), Nil)))
    // let s = Subst.empty()

    // println("${List<Any>.toString<VarIndex, Term>(Subst.unify(t1, t2, s).getOrThrow())}")

    let query = Stream.callFresh(
        {
            x =>
            // let list1 = StdTerms.Array2Term([StdTerms.mkConst("aAa"), StdTerms.mkConst("bBb")])
            let list2 = StdTerms.Array2Term([StdTerms.mkConst("cCc"), StdTerms.mkConst("dDd")])
            let list1 = ctor("Nil")
            appendo(list1, list2, x)
        }
    )

    let results = Stream.run(10, query)

    for (result in results) {
        println(result.ToString())
    }

    let query2 = Stream.callFresh( {
      q => appendo(
        ctor("Cons", ctor("1"), ctor("nil")),
        //ctor("Nil"),
        ctor("Cons", ctor("2"), ctor("nil")),
        //ctor("Nil"),
        q)
    })

    let results2 = Stream.run(1, query2)

    for (result in results2) {
        println(result.ToString())
    }

    println("FIN")
    return 0
}
