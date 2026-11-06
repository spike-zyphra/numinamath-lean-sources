import Mathlib


open Classical in


theorem number_theory_15467 : ((Finset.Icc 1 120).filter fun n => ∃ k, 120 ∣ n * 10 ^ k).card = 40 := by

  have h1 : ((Finset.Icc 1 120).filter fun n => ∃ k, 120 ∣ n * 10 ^ k) = Finset.filter (fun n => 3 ∣ n) (Finset.Icc 1 120) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · -- Forward implication: existence of k such that 120 divides n * 10^k implies 3 divides n
      intro h
      rcases h with ⟨⟨hn1, hn2⟩, ⟨k, hk⟩⟩
      have h2 : 3 ∣ n * 10 ^ k := by
        omega
      -- Since 10^k and 3 are coprime, 3 must divide n
      have h4 : Nat.Coprime 3 (10 ^ k) := by
        have h5 : Nat.Coprime 3 10 := by norm_num
        have h6 : Nat.Coprime 3 (10 ^ k) := by
          apply Nat.Coprime.pow_right
          all_goals omega
        simpa using h6
      have h7 : 3 ∣ n := by
        apply Nat.Coprime.dvd_of_dvd_mul_right h4 h2
      tauto
    · -- Backward implication: if 3 divides n, then there exists k such that 120 divides n * 10^k
      intro h3
      refine ⟨⟨by omega, by omega⟩, ⟨3, by omega⟩⟩
  rw [h1]
  native_decide