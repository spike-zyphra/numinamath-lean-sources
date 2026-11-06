import Mathlib

/-Let $a$ and $b$ be coprime positive natural numbers such that $a < b$. 
Let $g$ be a positive natural number. Define $x = a \cdot g$ and $y = b \cdot g$. Show that $y - x = (b-a) \cdot \gcd(x,y)$.-/

theorem number_theory_637665
  (a b g x y: ℕ) (h2: a < b) (hp: Nat.Coprime a b) (h3: 0 < g) (h4: x = a * g) (h5: y = b * g):
    y - x = (b - a) * x.gcd y := by

  suffices x.gcd y = g by
    rw [this]
    simp [h4, h5]
    zify
    have s1: ↑(b * g - a * g) = ((b: ℤ) * g - (a: ℤ) * g) := by
      rw [← Int.natCast_mul]
      rw [← Int.natCast_mul]
      apply Int.natCast_sub
      nlinarith
    have s2: ↑(b - a) = (b: ℤ) - (a: ℤ) := by
      apply Int.natCast_sub
      omega
    simp [s1, s2]
    ring

  -- then we show the gcd relation
  simp [h4, h5]
  have f1: (a * g).gcd (b * g) = g.gcd (b * g) := by
    rw [Nat.gcd_eq_iff]
    constructor
    .
      suffices g.gcd (b * g) ∣ g by
        have u: g ∣ a * g := by
          simp
        apply dvd_trans this u
      apply Nat.gcd_dvd_left
    .
      constructor
      .
        apply Nat.gcd_dvd_right
      .
        intro c c1 c2
        rw [Nat.dvd_gcd_iff]
        simp [c2]
        replace hp: gcd (a: ℤ) b = 1 := by
          rw [← Int.coe_gcd]
          suffices (a: ℤ).gcd ↑b = 1 by simp [this]
          rw [Int.gcd_natCast_natCast]
          apply Nat.Coprime.gcd_eq_one hp

        have i:= exists_gcd_eq_mul_add_mul (a: ℤ) b
        obtain ⟨x, y, s⟩ := i
        simp [hp] at s
        zify at c1 c2
        zify
        rw [show g = (1: ℤ) * g by simp]
        rw [s]
        ring_nf
        apply dvd_add
        .
          suffices (a: ℤ) * g ∣ ↑a * x * ↑g by
            apply dvd_trans c1 this
          rw [show (a: ℤ) * x * g = (a: ℤ) * g * x by ring]
          simp
        .
          suffices (b: ℤ) * g ∣ ↑b * y * ↑g by
            apply dvd_trans c2 this
          rw [show (b: ℤ) * y * g = (b: ℤ) * g * y by ring]
          simp

  rw [f1]
  apply Nat.gcd_mul_left_right