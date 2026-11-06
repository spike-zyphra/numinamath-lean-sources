import Mathlib

/- Let $a$ and $k$ be positive integers such that $a^{2}+k$ divides $(a-1) a(a+1)$. Prove that $k \geq a$. -/
theorem Number_theory_241485 (a k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (h : a^2 + k ∣ (a - 1) * a * (a + 1)) : k ≥ a := by
    -- The key identity --
    have id: (a - 1) * a * (a + 1) = a * (a ^ 2 + k) - (k + 1) * a := by
        symm
        calc
            a * (a ^ 2 + k) - (k + 1) * a = a ^ 3 + a * k - (k + 1) * a := by ring_nf
                                       _  = a ^ 3 + a * k - (a * k + a) := by ring_nf
                                       _  = (a ^ 3 + a * k) - (a * k + a) := by omega
                                       _  = (a ^ 3 + a * k) - a * k - a := by rw [← Nat.sub_sub]
                                       _  = a ^ 3 + a * k - a * k - a := by ring_nf
                                       _  = a ^ 3 - a := by rw [Nat.add_sub_cancel]
                                       _  = a * (a ^ 2 - 1) := by ring_nf;rw [Nat.mul_sub];ring_nf
                                       _  = a * (a - 1) * (a + 1) := by nth_rewrite 1[show 1 = 1 ^ 2 by omega]; rw[Nat.sq_sub_sq]; ring_nf
                                       _  = (a - 1) * a * (a + 1) := by ring_nf
    rw [id] at h
    have h2: a ^ 2 + k ∣ (k + 1) * a := by
        have eq: (k + 1) * a = (a * (a ^ 2 + k)) - ((a * (a ^ 2 + k)) - (k + 1) * a) := by
             symm
             have ineq: (k + 1) * a ≤ a * (a ^ 2 + k) := by
                have ineq3: a ≤ a ^ 3 := by
                   calc
                    a = a ^ 1 := by ring
                    _ ≤ a ^ 3 := by apply Nat.pow_le_pow_of_le_right; omega; omega
                calc
                    (k + 1) * a = a * k + a := by ring
                              _ ≤ a * k + a ^ 3 := by simp [ineq3]
                              _ = a * (a ^ 2 + k) := by ring_nf
             rw [← Nat.Simproc.add_sub_le (a * (a ^ 2 + k)) ineq]
             simp
        have h3: a ^ 2 + k ∣ a * (a ^ 2 + k) := by simp
        rw [eq]
        apply Nat.dvd_sub
        simp
        exact h3
        exact h
    apply Nat.le_of_dvd at h2
    have u: a ≤ k + 1 := by
        have u1: a * a ≤ a * (k + 1) := by
            calc
                a * a ≤ a * a + k := by simp
                    _ = a ^ 2 + k := by ring_nf
                    _ ≤ (k + 1) * a := by exact h2
                    _ = a * (k + 1) := by ring_nf
        apply Nat.le_of_mul_le_mul_left at u1
        simp [ha] at u1
        exact u1
    by_contra! v
    have v1: a = k + 1 := by omega
    simp [v1] at h2
    ring_nf at h2
    replace h2: 1 + k ^ 2 + k * 3 ≤ 1 + k ^ 2 + k * 2 := by omega
    simp at h2
    apply Nat.le_of_mul_le_mul_left at h2
    simp [hk] at h2
    have h4: 0 < k + 1 := by omega
    nlinarith