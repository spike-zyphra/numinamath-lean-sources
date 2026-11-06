import Mathlib

/- Prove that the product of three consecutive positive integers is never a perfect square. -/
theorem number_theory_75066 (n: ℤ) (hn : 0 < n) :
    ¬ IsSquare (n * (n + 1) * (n + 2)) := by
      by_contra! h
      rw [isSquare_iff_exists_sq] at h
      obtain ⟨k, h⟩ := h

      -- show that n + 1 is coprime to n and n + 2
      have o: IsCoprime (n * (n + 2)) (n + 1):= by
        apply IsCoprime.mul_left
        . rw [show n + 1 = n * 1 + 1 by omega]
          have l: IsCoprime n 1 := by
            apply isCoprime_one_right
          apply IsCoprime.mul_add_left_right l
        . set u:= n + 1 with hu
          rw [show n + 2 = u + 1 by simp [hu]; omega]
          rw [isCoprime_comm]
          rw [show u + 1 = u * 1 + 1 by omega]
          have l: IsCoprime u 1 := by
            apply isCoprime_one_right
          apply IsCoprime.mul_add_left_right l

      -- then we show that n * (n + 2) is a perfect square
      rw [show n * (n + 1) * (n + 2) = (n * (n + 2)) * (n + 1) by ring] at h
      have f: ∃ d: ℤ, 0 ≤ d ∧ n * (n + 2) = d ^ 2 := by
        apply Int.sq_of_coprime at h
        obtain ⟨e,f⟩ := h
        rcases f with f | f
        . set d:= |e| with hd
          replace f: n * (n + 2) = d ^ 2 := by
            rw [f]
            rw [sq_eq_sq_iff_abs_eq_abs]
            simp [hd]
          have o: 0 ≤ d := by simp [hd]
          use d
        . have o1: 0 < n * (n + 2) := by nlinarith
          rw [f] at o1
          absurd o1
          simp
          apply sq_nonneg
        exact o
      obtain ⟨d,hd,f⟩ := f
      set m:= n + 1 with hm
      replace hm: n = m - 1 := by omega
      simp [hm] at f
      have eq: (m - 1) * (m - 1 + 2) = m ^ 2 - 1 := by ring

      -- then we show contradiction at f
      replace f: m ^ 2 = d ^ 2 + 1 := by
        rw [← f]
        have o: 1 ≤ m ^ 2 := by
          have l: 1 ≤ m := by linarith
          apply one_le_pow₀
          exact l
        omega
      have ld: 0 < d := by
        by_contra! i
        replace i: d = 0 := by
          omega
        simp [i] at f
        simp [f] at hm
        simp [hm] at hn
        rcases f with f | f
        . simp [f] at hn
        . simp [f] at hn
      have l1: d ≤ m := by
        have i: d ^ 2 ≤ m ^ 2 := by
          rw [f]
          omega
        rw [pow_le_pow_iff_left₀] at i
        exact i
        omega
        omega
        norm_num
      have l2: m < d + 1 := by
        by_contra! i
        replace i: (d + 1) ^ 2 ≤ m ^ 2 := by
          rw [← pow_le_pow_iff_left₀] at i
          exact i
          omega
          omega
          norm_num
        rw [f] at i
        nlinarith
      nlinarith [l1,l2]