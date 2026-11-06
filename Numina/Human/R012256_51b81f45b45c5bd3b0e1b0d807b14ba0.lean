import Mathlib

open Polynomial Finset

/-Let $f$ be a polynomial with integer coefficients such that the greatest common divisor of all its coefficients is 1 . For any $n \in \mathbb{N}, f(n)$ is a multiple of 85 . Find the smallest possible degree of $f$.-/
theorem number_theory_608540 : IsLeast {n | ∃ f : ℤ[X], n = f.natDegree ∧ (∀ m : ℕ,
    85 ∣ f.eval (m : ℤ)) ∧ (f.content = 1)} 17 := by
-- Split the goal to an existential subgoal and a lower bound subgoal
  simp [IsLeast, lowerBounds, and_assoc]; constructor
  -- Fulfill the existential goal with the product polynomial $P=X*(X+1)*...*(X+16)$
  · let P := (X:ℤ[X])*(X+1)*(X+2)*(X+3)*(X+4)*(X+5)*(X+6)*(X+7)*(X+8)*(X+9)*
    (X+10)*(X+11)*(X+12)*(X+13)*(X+14)*(X+15)*(X+16)
    have Pdeg : P.natDegree = 17 := by
      dsimp [P]; compute_degree; all_goals norm_num
    use P; split_ands; symm; exact Pdeg
    -- Prove that $P(m)$ is a multiple of $85$ for any $m$
    · intro m; simp [P]; rw [show (85:ℤ) = 5*17 by simp]
      apply IsCoprime.mul_dvd; norm_num
      · rw [Int.dvd_iff_emod_eq_zero]
        rw [Int.mul_emod, Int.add_emod]
        nth_rw 2 [Int.mul_emod]; rw [Int.add_emod]
        nth_rw 3 [Int.mul_emod]; rw [Int.add_emod]
        nth_rw 4 [Int.mul_emod]; rw [Int.add_emod]
        nth_rw 5 [Int.mul_emod]; rw [Int.add_emod]
        have := Int.emod_lt_of_pos m (show 5>0 by simp)
        have := Int.emod_nonneg m (show 5≠0 by simp)
        interval_cases (m:ℤ) % 5
        all_goals norm_num
      rw [show (17:ℤ) = (17:ℕ) by rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast; generalize (m : ZMod 17) = l
      fin_cases l; any_goals simp
      all_goals reduce_mod_char
  -- Prove that the gcd of all coefficients of $P$ is $1$
    rw [← isPrimitive_iff_content_eq_one, IsPrimitive]
    intro r hr; rw [C_dvd_iff_dvd_coeff] at hr
    specialize hr 17; apply isUnit_of_dvd_one
    convert hr; symm; dsimp [P]; compute_degree
    all_goals norm_num
-- To show $17$ is a lower bound for all such polynomials, we first reduce such a polynomial to $ZMod 17$
  intro d P hd hP1 hP2; rw [hd]; clear hd d
  let Pm := Polynomial.map (Int.castRingHom (ZMod 17)) P
-- Prove that the reduced polynomial is nonzero
  have Pmne0 : Pm ≠ 0 := by
    intro h; simp [Pm, ext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [← C_dvd_iff_dvd_coeff, ← dvd_content_iff_C_dvd] at h
    simp [hP2] at h; omega
-- Prove the reduced polynomial's degree is at most the same with the original polynomial
  have Pmdeg : Pm.natDegree ≤ P.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn; simp [Pm]
    rw [coeff_eq_zero_of_natDegree_lt]; rfl
    exact hn
  apply le_trans _ Pmdeg
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
-- It suffices to show that any element of $ZMod 17$ is a root of $Pm$, therefore $Pm$ has degree at least $17$
  suffices : Pm.roots.toFinset = univ
  · calc
      _ = #(@univ (ZMod 17) _) := by simp
      _ = #Pm.roots.toFinset := by symm; congr
      _ ≤ Pm.roots.card := Multiset.toFinset_card_le Pm.roots
      _ ≤ _ := card_roots' Pm
-- Use `eval_intCast_map` to simplify the goal and apply `hP1` to finish the goal
  simp [Finset.ext_iff]; intro a
  constructor; exact Pmne0
  rw [show a = (a.val:ℤ) by symm; exact ZMod.natCast_zmod_val a]
  dsimp [Pm]; rw [eval_intCast_map]
  simp only [ZMod.intCast_cast, eq_intCast]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
  specialize hP1 a.val; omega