import Mathlib

/- f s k is the list of all lists of length k that contain only elements of s. -/
def f (s : List ℕ) : ℕ → List (List ℕ)
| 0 => [[]]
| n + 1 => do
  -- Pick an element x of s and a list y of f s n.
  let x ← s
  let y ← f s n
  -- Return the list x :: y.
  return x :: y

/- Lemma 1: l has length k and is a subset of s implies that l is an element of f s k. -/
lemma lemma_1 {k : ℕ} {l : List ℕ} (h₁ : l.length = k) (h₂ : l ⊆ s) : l ∈ f s k := by
  -- Let's do induction on k.
  induction k generalizing l with
  | zero =>
    -- Base case: k = 0, l must be empty.
    simp [f]
    exact List.length_eq_zero.mp h₁
  | succ k ih =>
    -- Inductive step: k = n + 1.
    -- We have l = a :: t, where t has length n.
    rcases List.exists_of_length_succ _ h₁ with ⟨a, t, rfl⟩
    simp at h₁ h₂
    simp [f]
    -- The conclusion follows from the inductive hypothesis.
    exact ⟨h₂.1, ih h₁ h₂.2⟩

/- A 12-digit positive integer consisting only of digits 1,5 and 9 is divisible by 37. Prove that the sum of its digits is not equal to 76. -/
theorem number_theory_606393 (n : ℕ) (h₀ : 0 < n) (h₁ : (Nat.digits 10 n).length = 12) (h₂ : Nat.digits 10 n ⊆ [1, 5, 9]) (h₃ : 37 ∣ n) :
    (Nat.digits 10 n).sum ≠ 76 := by
  -- The idea is to enumerate all the possible 12-digit numbers that have only digits 1,5 and 9.
  set l := Nat.digits 10 n
  -- We can recover n from l.
  have hl : Nat.ofDigits 10 l = n := Nat.ofDigits_digits _ _
  rw [← hl] at h₃
  -- Use lemma 1 to show that l is an element of f [1, 5, 9] 12.
  have h₄ : l ∈ f [1, 5, 9] 12 := lemma_1 h₁ h₂
  -- Remove the redundant hypotheses.
  clear_value l
  clear n h₀ hl h₁ h₂
  -- We can now enumerate all the possible 12-digit numbers that have only digits 1,5 and 9.
  revert h₃
  revert l
  native_decide
