import Mathlib

/-Trouver tous les quadruplets d'entiers relatifs $(a, b, c, p)$ tels que $p$ soit un nombre premier et pour lesquels

$$
73 p^{2}+6=9 a^{2}+17 b^{2}+17 c^{2}
$$-/
theorem number_theory_604818 (a b c : ℤ) (p : ℕ) (hp : p.Prime) :
(73 : ℤ) * p ^ 2 + 6 = 9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2 ↔ (a = 1 ∨ a = -1) ∧ p = 2 ∧
((b = 1 ∧ c = 4) ∨ (b = -1 ∧ c = 4) ∨ (b = 1 ∧ c = -4) ∨ (b = -1 ∧ c = -4) ∨
(b = 4 ∧ c = 1) ∨ (b = -4 ∧ c = 1) ∨ (b = 4 ∧ c = -1) ∨ (b = -4 ∧ c = -1)) := by
-- Prove that a square modulo $8$ can only be $0$, $1$ or $4$
  have sqmod8 : ∀ n : ℤ, n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
    intro n; rw [← Int.ediv_add_emod n 8]; ring_nf; rw [show (16:ℤ) = 2*8 by simp]
    rw [show (64:ℤ) = 8*8 by simp, ← mul_assoc, ← mul_assoc, ← add_mul, add_comm]
    rw [Int.add_mul_emod_self]; have := Int.emod_lt_of_pos n (show 0<(8:ℤ) by simp)
    have := Int.emod_nonneg n (show (8:ℤ)≠0 by simp)
    interval_cases n % 8; all_goals simp_all
-- Prove that an odd square modulo 8 is $1$
  have oddsqmod8 : ∀ m : ℕ, Odd m → (m : ℤ) ^ 2 % 8 = 1 := by
    intro m hm; rcases hm with ⟨t, ht⟩; norm_cast
    rw [ht, Nat.pow_mod, Nat.add_mod]
    nth_rw 1 [show 8 = 2*4 by simp, Nat.mul_mod_mul_left]
    have := Nat.mod_lt t (show 4>0 by simp)
    interval_cases t % 4; all_goals norm_num
  constructor
  -- Take modulo $8$ on both sides of the equation
  · intro heq; let heqmod8 := heq; apply_fun fun t => t % 8 at heqmod8
    by_cases ppar : Odd p
    -- Assume $p$ is odd, then derive a contradiction from heqmod8 by checking all possible cases of sqmod8
    · rw [Int.add_emod] at heqmod8; nth_rw 2 [Int.add_emod] at heqmod8
      nth_rw 3 [Int.add_emod] at heqmod8; rw [Int.mul_emod] at heqmod8
      nth_rw 2 [Int.mul_emod] at heqmod8; nth_rw 3 [Int.mul_emod] at heqmod8
      nth_rw 4 [Int.mul_emod] at heqmod8; rw [oddsqmod8 p ppar] at heqmod8
      rcases sqmod8 a with _|_|_ <;> rcases sqmod8 b with _|_|_ <;> rcases sqmod8 c with _|_|_
      all_goals simp_all
  -- Therefore $p$ has to be $2$ since it is an even prime
    rw [Nat.not_odd_iff_even, hp.even_iff] at ppar; simp [ppar] at heq
  -- Take natAbs on both sides of heq and simplify
    apply_fun fun t => t.natAbs at heq; repeat rw [Int.natAbs_add_of_nonneg] at heq
    repeat rw [Int.natAbs_mul] at heq; repeat rw [Int.natAbs_pow] at heq
  -- Prove that $a.natAbs$ is less than $6$
    simp at heq; have : a.natAbs < 6 := by
      by_contra!; suffices : 298 < 9 * a.natAbs ^ 2 + 17 * b.natAbs ^ 2 + 17 * c.natAbs ^ 2; linarith
      calc
        _ < 9 * 6 ^ 2 := by simp
        _ ≤ 9 * a.natAbs ^ 2 := by rw [mul_le_mul_left, pow_le_pow_iff_left₀]; all_goals linarith
        _ ≤ _ := by ring_nf; rw [add_assoc]; apply le_add_right; rfl
  -- Take modulo $17$ on both sides of heq and prove that $a.natAbs$ is $1$
    let heqmod17 := heq; apply_fun fun t => t % 17 at heqmod17
    rw [add_assoc, ← mul_add, Nat.add_mul_mod_self_left] at heqmod17; norm_num at heqmod17
    interval_cases absa : a.natAbs; any_goals simp at heqmod17
  -- Prove that $a.natAbs$ is less than $5$
    have : b.natAbs < 5 := by
      by_contra!; suffices : 298 < 9 * 1 ^ 2 + 17 * b.natAbs ^ 2 + 17 * c.natAbs ^ 2; linarith
      calc
        _ < 17 * 5 ^ 2 := by simp
        _ ≤ 17 * b.natAbs ^ 2 := by rw [mul_le_mul_left, pow_le_pow_iff_left₀]; all_goals linarith
        _ ≤ _ := by ring_nf; nth_rw 2 [add_comm]; rw [add_assoc]; apply le_add_right; rfl
  -- Prove that $c.natAbs$ is less than $5$
    have : c.natAbs < 5 := by
      by_contra!; suffices : 298 < 9 * 1 ^ 2 + 17 * b.natAbs ^ 2 + 17 * c.natAbs ^ 2; linarith
      calc
        _ < 17 * 5 ^ 2 := by simp
        _ ≤ 17 * c.natAbs ^ 2 := by rw [mul_le_mul_left, pow_le_pow_iff_left₀]; all_goals linarith
        _ ≤ _ := by ring_nf; nth_rw 2 [add_comm]; rw [add_assoc]; apply le_add_right; rfl
  -- Check all possible values of $b.natAbs$ and $c.natAbs$ to finish the goal
    zify at absa; rw [abs_eq] at absa
    split_ands; exact absa; exact ppar; any_goals positivity
    interval_cases absb : b.natAbs <;> interval_cases absc : c.natAbs; any_goals simp_all
    all_goals zify at absb absc; rw [abs_eq] at absb absc
    any_goals rcases absb <;> rcases absc
    all_goals omega
-- Conversely, it is straightforward to check that the listed values for $a$, $b$, $c$ and $p$ satisfies the equation in question
  rintro ⟨ha, hp, hbc⟩; simp [hp]; rcases ha <;> rcases hbc with ⟨_,_⟩|⟨_,_⟩|⟨_,_⟩|⟨_,_⟩|⟨_,_⟩|⟨_,_⟩|⟨_,_⟩|⟨_,_⟩
  all_goals simp_all
