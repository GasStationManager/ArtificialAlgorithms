/-
One-Dimensional Dynamic Programming, with Rod-Cutting Example
Parts done by Sonnet 3.5, with LeanTool
See blog post https://gasstationmanager.github.io/ai/2024/12/09/dp2.html for details
-/

import Mathlib.Tactic

def Cell (ftarget: α→β):=
  {c: α × β//ftarget c.fst =c.snd}

def DPArray (ftarget:Nat->β) (n:Nat)
:= {arr:Array (Cell ftarget)//
    arr.size=n+1 ∧
    ∀ i: Fin arr.size,
    i = arr[i].val.fst
   }

theorem DPArray_get {ftarget: Nat → β} {n: Nat} 
    (arr: DPArray ftarget n) (i: Fin arr.val.size):
    ftarget i = arr.val[i].val.snd := by
  have h1 := arr.property.2 i  -- i = arr[i].val.fst
  have h2 := arr.val[i].property -- ftarget (arr[i].val.fst) = arr[i].val.snd
  have h3 : ftarget i = ftarget (arr.val[i].val.fst) := by
    congr
    
  rw [h3]
  exact h2

def DPArray_push {ftarget: Nat → β} {n: Nat}
    (arr: DPArray ftarget n) (c: Cell ftarget) (h: c.val.fst = n + 1):
    DPArray ftarget (n + 1) :=  
  let newArr := arr.val.push c  
  have hsize : newArr.size = (n + 1) + 1 := by
    rw [Array.size_push]
    rw [arr.property.1]

  have hind : ∀ i: Fin newArr.size, i = newArr[i].val.fst := by
    intro i
    let i' := i.val
    have hi' : i' < newArr.size := i.isLt
    have hsz : newArr.size = arr.val.size + 1 := by grind [Array.size_push]

    if h1 : i' < arr.val.size then
      -- For indices less than original size
      have heq : newArr[i] = arr.val[i'] := by
        apply Array.getElem_push_lt
        
      rw [heq]
      have := arr.property.2 ⟨i', h1⟩
      exact this
    else
      -- For the last index
      have : i' = arr.val.size := by
        apply Nat.eq_of_lt_succ_of_not_lt
        · rw [hsz] at hi'
          exact hi'
        · exact h1
      have heq : newArr[i] = c := by
        simp only [Fin.getElem_fin]
        simp[i'] at this
        simp [this]
        apply Array.getElem_push_eq
      rw [heq]
      rw [arr.property.1] at this

      have : i.val = n + 1 := this
      have : i.val = c.val.fst := by
        rw [h]
        exact this
      exact this

  ⟨newArr, And.intro hsize hind⟩

def rodCutMap(prices:List (Nat×Nat))(n:Nat):Nat:=
  match hn:n with
  |0=>0
  |n'+1=>
    let pred := fun (p:Nat×Nat) =>  0 < p.fst ∧ p.fst ≤ n'+1
    let candidates:List (Subtype pred) := prices.filterMap (fun p=> if h: pred p then some ⟨ p, h⟩  else none)
    let values:=candidates.map (fun p=> p.val.snd+rodCutMap prices (n'+1-p.val.fst) )
    values.foldl (fun x y=>max x y) 0


def step (prices: List (Nat×Nat)) {n: Nat} (arr: DPArray (rodCutMap prices) n):
    DPArray (rodCutMap prices) (n+1) :=
  let n' := n
  let pred := fun (p:Nat×Nat) =>  0 < p.fst ∧ p.fst ≤ n'+1
  let candidates : List (Subtype pred) :=
    prices.filterMap (fun p=> if h: pred p then some ⟨p, h⟩ else none)

  let values := candidates.map (fun (p: Subtype pred) =>
    have h_bound : n'+1-(p.val.fst) < arr.val.size := by
      rw [arr.property.1]
      rcases p.property with ⟨h1, h2⟩
      have : p.val.fst ≤ n'+1 := h2
      have : 0 < p.val.fst := h1
      apply Nat.sub_lt_of_pos_le
      · exact this
      · exact h2
    let idx : Fin arr.val.size := ⟨n'+1-(p.val.fst), h_bound⟩
    p.val.snd + (arr.val[idx]).val.snd
  )

  let maxVal := values.foldl (fun x y=>max x y) 0


  let newCell : Cell (rodCutMap prices) :=
    ⟨(n+1, maxVal), by
      rw [rodCutMap]
      simp [n']
      -- For each candidate, array lookup gives same result as recursive call
      have h_lookup : ∀ (p: Subtype pred),
        let remaining := n'+1-(p.val.fst)
        let h_bound : remaining < arr.val.size := by {
          rw [arr.property.1]   
          rcases p.property with ⟨h1, h2⟩
          apply Nat.sub_lt_of_pos_le
          · exact h1
          · exact h2
        }
        rodCutMap prices remaining = (arr.val[remaining]).val.snd := by
        intro p
        exact DPArray_get arr ⟨n'+1-(p.val.fst), by {
          rw [arr.property.1]   
          rcases p.property with ⟨h1, h2⟩
          apply Nat.sub_lt_of_pos_le
          · exact h1
          · exact h2
        }⟩
      -- Therefore values lists are equal
      have h_values : values = candidates.map (fun p =>
        p.val.snd + rodCutMap prices (n'+1-p.val.fst)) := by
        simp only [values]
        congr
        funext p

        simp [h_lookup p]
      -- And therefore maxVal equals rodCutMap prices (n+1)
      
      simp[maxVal]
      rw [h_values]

    ⟩

  DPArray_push arr newCell (by grind)

def rodDP (prices:List (Nat×Nat)) (n:Nat):{x:Nat // rodCutMap prices n=x} :=
  match n with
  | 0 => ⟨0, by rw [rodCutMap]⟩ 
  | n'+1 =>
    -- Create initial array with just solution for 0
    let initCell : Cell (rodCutMap prices) := ⟨(0, 0), by rw [rodCutMap]⟩
    let initArr := Array.mk [initCell]
    have hsize : initArr.size = 0 + 1 := by grind
    have hind : ∀ i: Fin initArr.size, i = initArr[i].val.fst := by
      intro i
      have : i.val = 0 := by simp
      rw [this]
      simp [Array.get]
      rfl
    let arr0 : DPArray (rodCutMap prices) 0 := ⟨initArr, And.intro hsize hind⟩

    -- Build up array using step
    let rec buildArray (k: Nat) : DPArray (rodCutMap prices) k :=
      match k with
      | 0 => arr0
      | k'+1 => step prices (buildArray k')

    -- Get final array and extract solution
    let finalArr := buildArray n'
    let finalStep := step prices finalArr
    have h_idx : n'+1 < finalStep.val.size := by
      rw [finalStep.property.1] 
      simp
    let idx : Fin finalStep.val.size := ⟨n'+1, h_idx⟩
    ⟨finalStep.val[idx].val.snd, by
      have := DPArray_get finalStep idx
      have heq : idx.val = n'+1 := rfl
      rw [heq] at this
      exact this
    ⟩

