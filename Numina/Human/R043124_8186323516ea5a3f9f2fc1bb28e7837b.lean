import Mathlib
/- 10.4. Given natural numbers $a, b, c$ such that $a>1, b>c>1$, and the number $a b c+1$ is divisible by $a b-b+1$. Prove that $b$ is divisible by $a$.
(M. Antipov) -/
theorem number_theory_99523 (a b c : ℕ) (ha : a > 1) (hb : b > c) (hc : c > 1) (h : a * b - b + 1 ∣ a * b * c + 1) : a ∣ b:= by
  -- First, we rewrite a*b*c + 1 as b*(a*c - a + 1) + (a*b - b + 1)
  have h1 : a * b * c + 1 = b * (a * c - a + 1) + (a * b - b + 1):= by
    set A:= a - 1 with hA
    set C:= c - 1 with hC
    clear_value A C
    replace hA : a = A + 1 := by subst A ; omega
    replace hC : c = C + 1 := by subst C ; omega
    subst a c
    rw [show (A + 1) * b - b = A * b by ring_nf ; omega]
    rw [show (A + 1) * (C + 1) - (A + 1) = (A + 1) * C by ring_nf ; omega]
    linarith
  rw [h1] at h

  -- Trivially, a*b - b + 1 divides itself
  have g1 : a * b - b + 1 ∣ a * b - b + 1:= by simp

  -- Since a*b - b + 1 divides a*b*c + 1 = b*(a*c - a + 1) + (a*b - b + 1),
  -- it must also divide b*(a*c - a + 1)
  replace h : a * b - b + 1 ∣ b * (a * c - a + 1):= by exact (Nat.dvd_add_iff_left g1).mpr h

  -- Prove that a*b - b + 1 and b are coprime
  replace g1 : Nat.Coprime (a * b - b + 1) b:= by
    set A:= a - 1 with hA
    clear_value A
    replace hA : a = A + 1 := by subst A ; omega
    subst a
    rw [show (A + 1) * b - b = A * b by ring_nf ; omega]
    suffices Nat.Coprime 1 b by exact (Nat.coprime_mul_right_add_left 1 b A).mpr this
    simp

  -- Since a*b - b + 1 and b are coprime, and a*b - b + 1 divides b*(a*c - a + 1),
  -- it must divide a*c - a + 1
  replace h : a * b - b + 1 ∣ a * c - a + 1:= by exact Nat.Coprime.dvd_of_dvd_mul_left g1 h

  -- Express the divisibility as an equation with some natural number k
  replace h : ∃ k : ℕ, a * c - a + 1 = (a * b - b + 1) * k:= by exact h
  rcases h with ⟨k, hk⟩
  clear g1

  -- Prove that k > 0
  have hk1 : k > 0:= by
    by_contra H
    simp at H
    subst k
    simp at hk

  -- Prove that k < 2
  have hk2 : k < 2:= by
    by_contra H
    simp at H
    replace H : (a * b - b + 1) * 2 ≤ (a * b - b + 1) * k:= by exact Nat.mul_le_mul_left (a * b - b + 1) H
    rw [←hk] at H
    set A:= a - 1 with hA
    set C:= c - 1 with hC
    clear_value A C
    replace hA : a = A + 1 := by subst A ; omega
    replace hC : c = C + 1 := by subst C ; omega
    subst a c
    rw [show (A + 1) * b - b = A * b by ring_nf ; omega] at H
    rw [show (A + 1) * (C + 1) - (A + 1) = (A + 1) * C by ring_nf ; omega] at H
    have g1 : A ≥ 1:= by omega
    replace g1 : A * b ≥ 1 * b:= by exact Nat.mul_le_mul_right b g1
    simp at g1
    have g2 : b ≥ C:= by omega
    replace g2 : A * b ≥ A * C:= by exact Nat.mul_le_mul_left A g2
    linarith

  -- Since k > 0 and k < 2, we have k = 1
  replace hk1 : k = 1:= by omega
  subst k
  simp at hk

  -- From the equation a*c - a + 1 = a*b - b + 1, derive that a*(c-1) = (a-1)*b
  have g1 : a * (c - 1) = (a - 1) * b:= by
    set C:= c - 1 with hC
    set A:= a - 1 with hA
    clear_value A C
    replace hA : a = A + 1 := by subst A ; omega
    replace hC : c = C + 1 := by subst C ; omega
    subst a c
    ring_nf at hk
    rw [show 1 + A + A * C + C - (1 + A) = A * C + C by omega] at hk
    rw [show A * b + b - b = A * b by omega] at hk
    linarith

  -- From a*(c-1) = (a-1)*b, we get that a divides (a-1)*b
  replace g1 : a ∣ (a - 1) * b:= by rw [←g1] ; simp

  -- Prove that a and a-1 are coprime
  have g2 : Nat.Coprime a (a - 1):= by
    set A:= a - 1 with hA
    clear_value A
    replace hA : a = A + 1 := by subst A ; omega
    subst a
    refine Nat.coprime_self_add_left.mpr (by simp)

  -- Since a divides (a-1)*b and a is coprime to a-1, a must divide b
  exact Nat.Coprime.dvd_of_dvd_mul_left g2 g1
