import Mathlib

def nextPossibleNumber (l : List ℕ) (n : ℕ) : Prop :=
    (∀ x ∈ l, x < n) ∧ (∀ x ∈ l, ∀ y ∈ l, x ≠ y → n ≠ x + y)

instance : DecidablePred (nextPossibleNumber l) := by
  intro n
  
  simp [nextPossibleNumber]
  infer_instance

lemma existsNextPossibleNumber (l : List ℕ) : ∃ n, nextPossibleNumber l n := by
  
  have h := (l.toFinset).bddAbove
  rcases h with ⟨M, hM⟩
  simp [upperBounds] at hM
  
  use 2 * M + 1
  simp [nextPossibleNumber]
  constructor
  . 
    intro x hx
    apply hM at hx
    omega
  . 
    intro x hx y hy hxy
    apply hM at hx
    apply hM at hy
    omega

def nextNumber (l : List ℕ) : ℕ :=
    Nat.find (existsNextPossibleNumber l)

def firstNumbers : ℕ → List ℕ
| 0 => []
| 1 => [1]
| 2 => [2, 1]
| 3 => [4, 2, 1]
| 4 => [6, 4, 2, 1]
| n + 1 => let l := firstNumbers n
           nextNumber l :: l

def nthNumber (n : ℕ) : ℕ :=
    (firstNumbers n).headI

theorem number_theory_609681 :
    nthNumber 100 = 388 := by
  native_decide