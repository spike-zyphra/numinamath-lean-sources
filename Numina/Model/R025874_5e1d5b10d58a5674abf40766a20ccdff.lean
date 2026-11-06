import Mathlib

def is_superb (n : ℕ) := n ∈ Finset.Icc 1000 9999 ∧ 4 * (n / 100) = (n % 100)

theorem number_theory_111192 :
    Set.ncard {n | is_superb n} = 15 ∧ ∀ n, is_superb n → 13 ∣ n := by
  have h1 : {n | is_superb n} = Finset.filter (fun n => 4 * (n / 100) = (n % 100)) (Finset.Icc 1000 9999) := by
    ext n 
    simp [is_superb]
  have h2 : Set.ncard {n | is_superb n} = 15 := by
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide
  constructor 
  · exact h2
  · -- Show that any superb number is divisible by 13
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h1000, h9999⟩
    have h3 : n % 100 = 4 * (n / 100) := by 
      omega 
    have h4 : n = 104 * (n / 100) := by
      omega
    omega