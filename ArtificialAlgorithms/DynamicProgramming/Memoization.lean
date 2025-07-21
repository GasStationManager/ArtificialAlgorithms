/- 
Memoization, with examples
The second example is done by Claude Sonnet 3.5 on Claude.ai, with manual feedback of Lean error messages.
Content of this file is the source for the blog post https://gasstationmanager.github.io/ai/2024/12/03/memoization1.html
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Batteries.Data.HashMap
open Batteries

/-
# Proving Generic Memoization in Lean, and Teaching It to Sonnet

Lately I have been practicing coding and
proving in Lean. Doing the following exercise has influenced how I think about programming in Lean.

Consider memoization. This is a very general algorithmic technique:
given a recursive function, we use a map-like data structure
to cache its return values so that later calls can directly
look up the answer without needing to recompute it.
Very easy to code up in any language: just a couple of lines
added to the existing recursive function. And we get a
nice exponential performance boost: asymptotically similar
to what we get with a bottom-up dynamic programming rewrite.

Here's the excercise: apply memoization to a recursive
function in Lean, and prove that the memoized version is
equivalent to the original function.
We would like this to be easily adapted to other
recursive functions, or switched to use other data structures,
with minimal rewriting efforts.

Another part of my motivation for looking at this is from
my interest in [building coding AIs that are able to prove correctness of their own code](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html). Dynamic programming has the reputation of being on the harder side of algorithmic techniques to master. In my previous life teaching algorithms to undergrads, I used to introduce memoization as a simple way to do dynamic programming. Now, if the correctness proof of memoization can also be done in a simple, modular manner, perhaps this can be taught to the AIs.

## Fibonacci

Let's take the example of the classic recursive function
for the n-th Fibonacci number.

-/

namespace Memoization

def fibRec (n:Nat) :Nat := match n with
  |0=>1
  |1=>1
  |n'+2=>(fibRec (n'+1)) + (fibRec n')

/-
Here is an implementation of memoized fibonnaci using HashMap:
-/
def fib1(n:Nat): Nat:=
  let rec helper (n:Nat)(hm:HashMap Nat Nat):Nat×HashMap Nat Nat:=
    match n with
    |0|1=>(1,hm)
    |n'+2=>
      match hm.find? (n'+2) with
      |some x=>(x,hm)
      |none=>
        let (f1,hm1):=helper (n'+1) hm
        let (f2,hm2):=helper n' hm1
        let r:=f1+f2
        let hm3:=hm2.insert (n'+2) r
        (r,hm3)
  (helper n mkHashMap).1
/-
Note that the content of the hash map will change throughout
the execution of the function, as more and more solutions are filled in. Being a pure functional programming language,
we pass around the HasMap objects instead of having a mutable variable. Another way of simulating mutability is
with a State Monad, which results in the following equivalent but slightly shorter code:
-/
def fib2 (n:Nat): Nat :=
  let rec helper (n:Nat): StateM (HashMap Nat Nat) Nat:=
    match n with
    |0|1 => pure 1
    |n'+2 => do
      let hm ← get
      match hm.find? (n'+2) with
      |some x=> return x
      |none=>
        let f1← helper (n'+1)
        let f2← helper n'
        let r:=f1+f2
        let hm2← get
        set (hm2.insert (n'+2) r)
        return r
  (helper n mkHashMap).1

/-
## Proof Goal

We would like to prove that the memoized fibonacci function
computes the same values as the original one.

theorem fib2_correct(n:Nat):
  fib2 n = fibRec n := sorry


Feel free to try proving it yourself before coming back.

For me, I had a hard time initially. I was eventually
able to power through it into a 200-line proof, but it feels
unsatisfactory:
- the proof cannot be easily adapted to other functions
- the theorem feels like it should be obviously true,
but the proof is complicated.

Is there a simple proof?
If you prompt GPT 4o with the task of coming up with a rigorous mathematical proof of this fact, it will give something less than rigorous.

I think the difficulty with a formal proof stems from the following. At a high level, we can break the proof task into two things:
1. We need to verify that the body of `fib1.helper` (or `fib2.helper`) is doing the same computation as the body of `fibRec`. We can do this by induction on the input argument `n`, and plugging in the function definitions. With `fib2` this is further complicated by having to unfold the syntactic sugar provided by the monad. Furthermore, the main difficulty is that this requires we show that the items we pulled from the HashMap are correct solutions to the corresponding subproblems. Which brings us to:
2. We need to prove that the HashMap provides the correct solutions to subproblems. In particular, that its
`.find? y` method returns either `none` or a value that equals `fibRec y`. Since `fib1`/`fib2` are called with the HashMap in all sorts of different states, a simple induction on `n` is not sufficient and we need to think more carefully about what statement to prove.
After a bit of thinking we realize we are trying
to prove an invariant property.
We could state the invariance as "If the HashMap satisfies the above property before the call to `helper`, then `helper` returns a HashMap that satisfies the same property". But to prove this, we will need to reason
about what `helper` does, and in particular point 1 above.

This coupling between the two subtasks complicates our proof, forcing us to juggle multiple things at the same time and having to repeat ourselves at places.

Eventually it clicked for me: the easiest way to prove this is in the style of programming with dependent types: attach logical properties to our data by subtyping.
First a brief introduction to subtyping in Lean:
given a type like `Nat`, you can create a subtype by
specifying a property that the members of the subtype mush satisfy, e.g. `{x:Nat // x > 0}` for positive natural numbers. Subtyping a function's return type effectively specifies the postcondition for the function. We can also subtype data structures to specify invanrances.
And we can prove the resulting proof obligations inside the function definition, resulting in a style that interleaves code and proof.

In our case, to prove property 2 above, all we need is to provide a version of `find?` such that `find? y` returns
a member of the subtype `{x:Nat // fibRec y=x}`.
In turn, we can achieve this by subtyping our HashMap.
To go one step further, instead of subtyping HashMap,
we can subtype the data that the HashMap stores. This way, we could easily substitute HashMap with another data structure without missing a beat.

For memoization, the key property for the data is: for a pair `k, v` stored in your data structure, `ftarget k = v` where `ftarget` is the recursive function you are proving equivalence to.

The following is my implementation. It starts with an important definition: a pair of values with a property attached to it.
-/

def MCell (ftarget: α->β):=
  {c: α × β//ftarget c.fst =c.snd}

/-
I am using HashMap here, but we could easily substitute in other data structures.

The HashMap stores key of type α, and value of type `MCell ftarget`, with key equal to the first element of the MCell.
A slight redundancy; in theory we might like to attach a property directly relating the key and the value, but that may require changing part of the HashMap implementation.
The current one is convenient and sufficient for our purpose.
-/
abbrev WeakMHMap[BEq α][Hashable α] (ftarget:α->β)
  := HashMap α (MCell ftarget)

/-
Here is a version of the `find?` method that guarantees that the returned value is
a solution to the requested subproblem.
-/
def WeakMHMap_find? [BEq α][Hashable α][LawfulBEq α](ft:α->β)(hm: WeakMHMap ft)(a:α)
:Option {b:β//ft a=b}:=
  match hf: hm.find? a with
  |none=>none
  |some x=>
    if heq: a == x.val.fst then
      have :ft a=x.val.snd:=by{
        have hx:=x.2
        simp at heq
        simp[heq,hx]
      }
      some ⟨ x.val.snd, this⟩
    else
      none

/-
With the way we will be using it, the key will always equal the first element of the MCell pair. But proving that fact will require going into the details of the data structure. To make things simple, I just checked for equality using an `if` here.

Note that the guarantee this function provides is that *if* an element is found, it will have the nice property. However it does not guarantee that an element will be found if you inserted it earlier.
To prove equivalence of memoization to the recursive function, we only need the former. The latter may become useful when we want to provide performance guarantees; that is the topic for an upcoming post.

Now we are ready to define the helper function for fib.
-/
def fibWMHMap(a:Nat)
:StateM (WeakMHMap fibRec) {b:Nat // fibRec a=b} :=
  match a with
  |0=>pure ⟨ 1, by simp[fibRec]⟩
  |1=>pure ⟨ 1, by simp[fibRec]⟩
  |a'+2=>do
    let memo ← get
    match hf: WeakMHMap_find? fibRec memo (a'+2) with
    | some x=>
      return x
    | none=>
      let r1← fibWMHMap (a'+1)
      let r2← fibWMHMap a'
      let r:= r1.val+r2.val
      let m2 ← get

      have hr: fibRec (a'+2)=r :=by{
        rcases r1 with ⟨ r1', r1p⟩
        rcases r2 with ⟨ r2', r2p⟩
        simp[r,r1p,r2p,fibRec]
      }
      let c:MCell fibRec:=⟨ (a'+2,r),hr⟩
      set (m2.insert (a'+2) c)
      return ⟨r, hr⟩

/-
And the main fib function. The return type
guarantees equivalence with the recursive version `fibRec`.
-/
def fib_main(a:Nat):{b:Nat//fibRec a=b}:=
  let hm:WeakMHMap fibRec:=mkHashMap
  let r:=fibWMHMap a hm
  r.1

/-
Compare this with our memoized Fibonacci implementation without proof, `fib2`. We see that surprisingly little
additional proof was required. Besides changing the return types and data structure to their corresponding subtypes,
the main additional proof was the block `have hr: ...`.
This three-line proof was needed to establish point 1 above, that the body of functions `fibRec` and `fibWMHMap`
are doing the same computations.

Outside the function, the definition `MCell` and the function `WeakMHMap_find?` did the bulk of work establishing point 2. Both are short and furthermore highly reusable.

Why did this approach succeed in making the proof simple?
I mentioned above that the challenge that my earlier attempt ran into was that the two subtasks are coupled with each other.
With this implementation, we see things more clearly now:
The logical argument for point 1 naturally follows the control flow of the two functions. The logical argument for point 2 naturally follows the data structure.
By subtyping, we allow the logical argument for point 2 to stick close to the data.
This then finally allows the two subtasks to be de-coupled.

## Binomial Coefficient

Our `MCell`, `WeakMHMap`, and `WeakMHMap_find?` can be reused
to prove the correctness of memoization for other functions.

Let's take the following recursive definition of the binomial coefficient (AKA m choose n, Pascal's triangle).
-/
def c: (Nat × Nat)->Nat
|(0,_)=>1
|(Nat.succ i', j)=>
    if hij: j == 0 || i'+1 == j then
      1
    else
      c (i', j) + c (i', (j-1))

/-
Here's the memoized version, with proof,
broadly following the same structure as our Fibonacci implementation.
-/

def cMemoHelper (p: Nat × Nat): StateM (WeakMHMap c) {r: Nat // c p = r} :=
  match hp: p with
  | (0, _) => pure ⟨1, by simp[c]⟩
  | (Nat.succ i', j) => do
    let memo ← get
    match hf: WeakMHMap_find? c memo p with
    | some x =>
        have : p = (Nat.succ i', j) := by simp[hp]
        have h : c (Nat.succ i', j) = x.val := by {
          rw [←this]
          exact x.property
        }
        return ⟨x.val, h⟩
    | none =>
      if hij: j == 0 || i'+1 == j then
        have h: c (Nat.succ i', j) = 1 := by simp[c, hij]
        return ⟨1, h⟩
      else
        let r1 ← cMemoHelper (i', j)
        let r2 ← cMemoHelper (i', j-1)
        let r := r1.val + r2.val
        let m2 ← get

        have hr: c (Nat.succ i', j) = r := by
          rcases r1 with ⟨r1', r1p⟩
          rcases r2 with ⟨r2', r2p⟩
          simp[c, hij, r, r1p, r2p]

        let cell: MCell c :=
          have h: c (p, r).fst = (p, r).snd := by {
            simp
            rw [hp]
            exact hr
          }
          ⟨(p, r), h⟩
        set (m2.insert p cell)
        return ⟨r, hr⟩

-- Main memoized binomial coefficient function
def cMemo (i j: Nat): {r: Nat // c (i,j) = r} :=
  let hm: WeakMHMap c := mkHashMap
  let r := cMemoHelper (i,j) hm
  r.1


end Memoization

/-
In fact, this memoized binomial coefficient implementation and proof was written by Claude Sonnet 3.5.

As promised at the beginning of this post, after I got a proof I was satisfied with, I tried to teach it to an AI.
Due to my limited resources, and the fact that this is an initial exploration, the learning was going to be via in-context learning rather than fine-tuning/RL of an LLM.

I chose Claude Sonnet because:
1. It has a relatively good grasp of Lean 4 syntax. A lot of current LLMs struggle with this because their training data likely contains a lot of Lean 3 code, which has incompatible syntax. Sonnet is very good at outputing Lean 4 code that is often valid or almost valid.
2. Sonnet is a very strong coder in general. And
I thought it would be a good fit with the style of proof we ended up choosing.


This was done on the Claude.ai web chat interface. I created a new Project and uploaded three text files:
- a prompt taken from the Sagredo project that reminds the LLM about important syntactic differences between Lean 3 and Lean 4
- a passage from my earlier essay talking about the style of programming with dependent types, with a simple toy example
- An earlier draft of this blog post, up to and including the memoized Fibonacci implementation and proof.

After a brief conversation to ensure Sonnet had a good understanding of the content of the files, I prompted with the recursive definition of binomial coefficient, and asked
it to implement the memoized version with proof.

Sonnet made a very respectabel first attempt.
It has valid syntax, and has the right structure.
Running it in Lean resulted in only a couple of complaints
that the proofs were not complete in certain parts.

The effect of certain tactics like `simp` can be hard to predict
without actually running it. So this kind of errors would be common
in human-written first drafts of Lean proofs as well.

In our case, while Sonnet's initial proof was morally correct,
a bit of additional work was needed to make the types and statements exactly line up.
E.g. we know in the context that `p=(Nat.succ i',j)`
but need to replace a statement involving one to a statment involving the other.

I prompted Sonnet with the error messages,
and an occasional hint about Lean syntax,
and Sonnet was able to fix the remaining errors,
and producing the correct proof shown above.

## Final Thoughts
- Sonnet has shown strong ability to produce code and proofs in Lean. I believe in certain situations it can already serve as a helpful coding assistant for Lean, just as it has been doing with other programming languages.
- Instead of manually sending code to Lean and error messages back to the LLM, we can automate it.
I recently wrote a simple script [LeanTool](https://github.com/GasStationManager/LeanTool)
to do exactly this, and it has been used in
[my autoformalization project](https://github.com/GasStationManager/FormalizeWithTest) to improve the quality
of LLM produced code.
- This is Part 1 of a series of posts, both exploring
proof techniques in Lean and LLMs' ability to learn these technqieus. Upcoming topics include: proving performance guarantees for memoization. Bottom-up dynamic programming.
And perhaps other algorithmic techniques like divide-and-conquer.

-/
