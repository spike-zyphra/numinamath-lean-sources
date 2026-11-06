import Mathlib

--We first prove two trivial bound on a.
lemma lem1 (a:ℝ) (ha: a ≤ -5 / 7):
7 * a + 4 ≤ (↑⌊a⌋) := by 

  by_cases al : a ≤ -5/6
  have cla1 : a - 1 ≤ ↑⌊a⌋ := by 
    refine (OrderedSub.tsub_le_iff_right a 1 ↑⌊a⌋).mpr ?_
    have : a < ↑⌊a⌋ + 1 := by exact Int.lt_floor_add_one a
    linarith
  have cla2 : 7 * a + 4 ≤ a - 1 := by linarith
  linarith

  push_neg at al
  have : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing a = -1 := by 
    refine Int.floor_eq_iff.mpr ?_
    simp
    constructor <;> linarith
  rw [this]
  simp
  linarith
lemma lem2 (a:ℝ) (ha: -4 / 7 < a):
{x:ℤ | x = ⌊a-4⌋ ∨ x = ⌊a-4⌋ +1 ∨ x = ⌊a-4⌋ + 2 ∨ x = ⌊a-4⌋+3} ⊆ {x | ↑x > a - 5 ∧ ↑x < 7 * a + 2} := by
  intro x
  simp
  intro h
  have cla1: a-5 < ⌊a⌋ - 4 := by 
    have : a < ⌊a⌋ + 1 := by exact Int.lt_floor_add_one a
    linarith
  have cla2: ⌊a⌋ - 4 + 3 < 7*a+2:= by 
    by_cases ag : -1/2 < a
    have : ⌊a⌋ ≤ a := by exact Int.floor_le a
    have : a - 4 + 3 < 7*a+2 := by linarith
    linarith
    push_neg at ag
    have : ⌊a⌋ = -1 := by 
      refine Int.floor_eq_iff.mpr ?_
      simp
      constructor <;> linarith
    rw [this]
    norm_num
    linarith

  rcases h with h | h | h | h <;> rw [h] <;> simp <;> constructor <;>
  linarith


theorem inequalities_157434 (a : ℝ):

{x:ℤ | x > a - 5 ∧ x < 7 * a + 2}.encard = 3
↔
-5/(7:ℝ) < a ∧ a ≤ - 4/(7:ℝ) := by

  constructor

  --From left to right.
  --The value of x can only be ⌊a-4⌋, ⌊a-4⌋+1, ⌊a-4⌋+2, so 7*a + 2 > ⌊a-4⌋+2. This gives the inequality for a.
  intro h
  by_cases au : a ≤ -5/7
  have cla1 : {x:ℤ | ↑x > a - 5 ∧ ↑x < 7 * a + 2} ⊆ {x:ℤ | x = ⌊a-4⌋ ∨ x = ⌊a-4⌋+1} := by 
    intro x
    simp
    intro xl xu
    have l1 : ⌊a⌋ - 4 ≤ x := by 
      field_simp
      refine Int.floor_le_iff.mpr ?_
      push_cast
      linarith
    have l2 : x < ⌊a⌋ - 2 := by 
      rify
      have : 7 * a + 4 ≤ (↑⌊a⌋) := by 
        apply lem1
        linarith
      linarith
    omega
  have cla2 : {x:ℤ | ↑x > a - 5 ∧ ↑x < 7 * a + 2}.encard ≤ {x:ℤ | x = ⌊a-4⌋ ∨ x = ⌊a-4⌋+1}.encard := by 
    apply Set.encard_mono
    exact cla1
  have cla3 : {x | x = ⌊a - 4⌋ ∨ x = ⌊a - 4⌋ + 1}.encard = 2 := by 
    rw [Set.encard_eq_two]
    use ⌊a - 4⌋, ⌊a - 4⌋+1
    simp
    ext x
    simp
  rw [h, cla3] at cla2
  norm_num at cla2
  by_cases al : -4/7 < a 
  have cla1 : {x:ℤ | x = ⌊a-4⌋ ∨ x = ⌊a-4⌋ +1 ∨ x = ⌊a-4⌋ + 2 ∨ x = ⌊a-4⌋+3} ⊆ {x | ↑x > a - 5 ∧ ↑x < 7 * a + 2} := by
    apply lem2
    linarith

  have cla2 : {x:ℤ | x = ⌊a-4⌋ ∨ x = ⌊a-4⌋ +1 ∨ x = ⌊a-4⌋ + 2 ∨ x = ⌊a-4⌋+3}.encard ≤ {x:ℤ | ↑x > a - 5 ∧ ↑x < 7 * a + 2}.encard := by 
    apply Set.encard_mono
    exact cla1
  have cla3 : {x:ℤ | x = ⌊a-4⌋ ∨ x = ⌊a-4⌋ +1 ∨ x = ⌊a-4⌋ + 2 ∨ x = ⌊a-4⌋+3}.encard = 4 := by 
    simp
    have : @OfNat.ofNat ℕ∞ 4 instOfNatAtLeastTwo = 3 + 1 := by norm_num
    rw [this]
    rw [Set.encard_eq_add_one_iff]
    use ⌊a-4⌋+3, {x:ℤ | x = ⌊a-4⌋ ∨ x = ⌊a-4⌋ +1 ∨ x = ⌊a-4⌋ + 2}
    simp [Set.encard_eq_three]
    constructor
    ext x
    simp
    tauto
    use ⌊a-4⌋, ⌊a-4⌋+1
    simp
    use ⌊a-4⌋+2
    simp
    ext x
    simp
  rw [h, cla3] at cla2
  norm_num at cla2

  push_neg at au al
  tauto 

  --From right to left, simple calcution to show that the set is ⌊a-4⌋, ⌊a-4⌋+1, ⌊a-4⌋+2.
  intro h
  obtain ⟨al,au⟩ := h
  rw [Set.encard_eq_three]

  use ⌊a-5⌋ + 1, ⌊a-5⌋ + 2, ⌊a-5⌋ + 3
  simp
  ext x
  simp

  have : ⌊a⌋ = -1 := by 
    refine Int.floor_eq_on_Ico (-1) a ?_
    simp
    constructor <;> linarith
  simp [this]

  constructor
  intro ⟨xl,xu⟩
  have xg: -6 < x := by 
    rify
    linarith
  have xl: x < -2 := by 
    rify
    linarith
  omega

  intro h

  rcases h with xe | xe | xe <;>
  rw [xe] <;>
  simp <;>
  constructor <;> 
  linarith

  
  