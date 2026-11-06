import Mathlib

/-
Let $D$ be a positive integer. We are looking for natural numbers $x, y, z$ such that $x < 10$, $y < 10$, $z < 10$, and the number $N = 100000x + 10000y + 3420 + z$ is divisible by $D$.
If $D = 783428$, show that the unique solution is $x=7, y=8, z=8$.
-/

theorem number_theory_638338 (D:ℕ) (Dpos: 0 < D) (x y z:ℕ) (xu: x < 10) (yu: y < 10) (zu: z < 10) (hD: D = 783428) (N: ℕ) (hN: N = 100000*x+10000*y+3420+z):
(D ∣ N)
↔
x = 7 ∧ y = 8 ∧ z = 8 := by

  constructor

  --From left to right, we show that N has to be equal to D.
  intro h
  obtain ⟨k,hk⟩ := h

  --If N/D ≥ 2, then N is too large.
  have ke : k = 1 := by 
    by_contra
    have kge2 : 2 ≤ k := by 
      by_cases ke0 : k = 0
      simp [ke0, hN] at hk
      omega
    have Nge : 1500000 ≤ N := by 
      rw [hk, hD]
      linarith
    omega
  simp [ke] at hk
  simp [hk,hD] at hN
  omega

  --From right to left, simple verification.
  intro ⟨xe,ye,ze⟩
  simp [hD,hN,xe,ye,ze]