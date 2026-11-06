import Mathlib

/-
II. (50 points) Given the algebraic expression $-x^{3}+100 x^{2}+x$, the letter $x$ is only allowed to take values within the set of positive integers. When the value of this algebraic expression reaches its maximum, what is the value of $x$? Prove your conclusion.
-/

theorem algebra_305180 (f : ℕ → ℤ) (hf : ∀x>0, f x = -x^3 + 100 * x^2 + x):
IsGreatest {y | ∃ x:ℕ, x > 0 ∧ f x = y} (f 67) := by
  
  unfold IsGreatest
  simp

  constructor
  use 67
  simp

  unfold upperBounds
  simp
  intro a apos

  --By the definition of f, we have the following expression of f (k+1) - f k.
  have lem: ∀k>0, f (k+1) - (f k) = - 3*k^2 + 197*k + 100 := by 
    intro k hk
    simp [hf, hk]
    ring_nf

  --Then we prove that f 67 is the greatest element in the image of f.
  have cla1: ∀m:ℕ, f (67 + m) ≤ f (67) := by 
    intro m
    induction' m with m hm

    simp

    have : f (67 + (m+1)) - f (67 + m) ≤ 0 := by 
      specialize lem (67 +m) (by linarith)
      nth_rw 1 [add_assoc] at lem
      rw [lem]
      ring_nf
      field_simp
      nlinarith
    linarith
  have cla2: ∀m:ℕ, m≤66 →  f (67 - m) ≤ f (67) := by 
    intro m
    induction' m with m hm

    simp

    intro h
    have ind: m ≤ 66 := by omega
    apply hm at ind

    have : 67 - m = 67 - (m+1) + 1 := by omega
    rw [this] at ind
    have : 0≤ f (67 - (m+1)+1) - f (67 - (m+1)) := by
      specialize lem (67-(m+1)) (by omega)
      rw [lem]
      ring_nf
      have : 0 < 67 - (1+m) := by omega
      have : @Nat.cast ℤ instNatCastInt (67 - (1 + m))  = 67 - (1 + m) := by omega
      rw [this]
      ring_nf
      nlinarith
    linarith
  
  by_cases age67: 67 ≤ a
  have exi: ∃m:ℕ, 67+m = a := by use a-67; omega
  obtain ⟨m,hm⟩ := exi
  specialize cla1 m
  rw [hm] at cla1
  exact cla1

  have exi: ∃m:ℕ, a = 67-m := by use 67-a; omega
  obtain ⟨m,hm⟩ := exi
  specialize cla2 m (by omega)
  rw [←hm] at cla2
  exact cla2
