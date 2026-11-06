import Mathlib

theorem negated_number_theory_45796 {a b : ℕ} 
    (ha : a = {n : ℕ | n ∈ Finset.range 400 ∧ 6 ∣ (n + 1)}.ncard)
    (hb : b = {n : ℕ | n ∈ Finset.range 400 ∧ 6 ∣ (n % 40 + 1)}.ncard) :
    (a - b : ℝ) / a < 0.1  := by
  have ha' : a = 66 := by
    rw [ha]
    have h1 : {n : ℕ | n ∈ Finset.range 400 ∧ 6 ∣ (n + 1)} = Finset.filter (fun n => 6 ∣ (n + 1)) (Finset.range 400) := by
      ext n
      simp
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide
  have hb' : b = 60 := by 
    rw [hb]
    have h1 : {n : ℕ | n ∈ Finset.range 400 ∧ 6 ∣ (n % 40 + 1)} = Finset.filter (fun n => 6 ∣ (n % 40 + 1)) (Finset.range 400) := by 
      ext n 
      simp
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide
  rw [ha', hb']
  norm_num