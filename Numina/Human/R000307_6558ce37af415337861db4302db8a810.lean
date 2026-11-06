import Mathlib


/-
  Determine all nonnegative integers  $n$ having two distinct positive divisors
  with the same distance from  $\tfrac{n}{3}$ . (Richard Henner)
-/
theorem number_theory_8870 (n : ℕ) :
    (∃ d1 d2 : ℕ, 0 < d1 ∧ d1 < d2 ∧ d1 ∣ n ∧ d2 ∣ n ∧ d2 - (n / (3 : ℝ)) = (n / (3 : ℝ)) - d1) ↔ n > 0 ∧ 6 ∣ n := by
  constructor <;> intro h
  · -- since 3 ∣ n, assume that n = 3c
    obtain ⟨d1, ⟨d2, ⟨hgt, ⟨hlt, ⟨_, ⟨hdvd2, hadd⟩⟩⟩⟩⟩⟩ := h
    have hadd : 3 * (d1 + d2) = 2 * n := by
      apply (@Nat.cast_inj ℝ _ _ (3 * (d1 + d2)) (2 * n)).mp
      simp
      linarith
    have hn : 3 ∣ n := by apply Nat.Coprime.dvd_of_dvd_mul_left (show Nat.Coprime 3 2 by decide) <| Dvd.intro (d1 + d2) hadd
    obtain ⟨c, hc⟩ := hn
    rw [hc] at hdvd2 hadd
    constructor
    · -- We first prove that n >0 
      by_contra heq
      push_neg at heq
      -- otherwise c = 0 and d1 = d2; contradiction 
      have heq : c = 0 := by linarith
      simp [heq] at hadd
      linarith
    · -- Since d2 ∣ 3c, we assume that 3c=d2 * c' 
      obtain ⟨c', hc'⟩ := hdvd2
      -- anylyze by cases, c' cannot be 0 or 1 
      match c' with
      | 0 | 1 => linarith
      | 2 =>
        -- If c'=2 then 2 ∣ c and 6 ∣ n 
        obtain ⟨k, hk⟩ : 2 ∣ c := by
          apply Nat.Coprime.dvd_of_dvd_mul_left (show Nat.Coprime 2 3 by decide)
          use d2
          nth_rw 2 [mul_comm]
          exact hc'
        simp [hk] at hc
        use k
        linarith
      | -- If c' ≥ 3, then d1 ≥ d2. contradiction 
        k + 3 =>
        have : 3 * d1 ≥ 3 * d2 := by
          calc
            3 * d1 = 3 * (d1 + d2) - 3 * d2 := by rw [mul_add, Nat.add_sub_cancel]
            _ = 2 * (d2 * (k + 3)) - 3 * d2 := by rw [hadd, <-hc'];
            _ = (2 * k + 3) * d2 := by rw [mul_comm, mul_assoc, add_mul, mul_comm, <-Nat.sub_mul]; simp; apply Or.inl; simp [mul_comm]
            _ ≥ 3 * d2 := by apply Nat.mul_le_mul_right d2; linarith
        linarith
  · -- verify the answer, assume n = 6c, then c > 0 
    rcases h with ⟨hpos, ⟨c, hc⟩⟩
    -- done by letting d1 = c and d2 = 3c 
    use c, 3 * c
    rw [hc]
    split_ands
    · linarith
    · linarith
    · exact Nat.dvd_mul_left c 6
    · apply Nat.mul_dvd_mul; all_goals trivial
    · field_simp
      ring