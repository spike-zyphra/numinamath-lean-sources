import Mathlib

/- Find all distinct prime numbers $p, q$ and $r$ such that

$$
3 p^{4}-5 q^{4}-4 r^{2}=26
$$ -/
theorem number_theory_605702 (p q r : ℕ) (ppr : p.Prime) (qpr : q.Prime) (rpr : r.Prime)
(hne : p ≠ q ∧ p ≠ r ∧ q ≠ r) : 3 * p ^ 4 - 5 * q ^ 4 - 4 * r ^ 2 = 26 ↔
(p = 5 ∧ q = 3 ∧ r = 19) := by
-- Prove that any square modulo $3$ is $0$ or $1$
  have sqmod3 : ∀ n, n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := by
    intro n; rw [Nat.pow_mod]; have := Nat.mod_lt n (show 0<3 by simp)
    interval_cases n % 3; all_goals simp
-- Prove that any square modulo $5$ is $0$, $1$ or $4$
  have sqmod5 : ∀ n, n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by
    intro n; rw [Nat.pow_mod]; have := Nat.mod_lt n (show 0<5 by simp)
    interval_cases n % 5; all_goals simp
  constructor
  -- Take modulo $3$ on both sides of heq, then apply sqmod3 to $q$ and $r$
  · intro heq; rw [Nat.sub_sub, Nat.sub_eq_iff_eq_add, ← add_assoc] at heq; let heq' := heq
    apply_fun fun t => t % 3 at heq'; simp [Nat.add_mod] at heq'
    rw [Nat.mod_mod, Nat.mod_mod, Nat.mod_mod, show q^4 = (q^2)^2 by ring] at heq'
    rw [Nat.mul_mod, Nat.pow_mod] at heq'; nth_rw 2 [Nat.mul_mod] at heq'
  -- Check all possible cases and the only possibility left is $q=3$
    rcases sqmod3 q with qm|qm <;> rcases sqmod3 r with rm|rm; any_goals simp [qm, rm] at heq'
    replace qm : q = 3 := by
      rw [← Nat.dvd_iff_mod_eq_zero] at qm; apply Nat.prime_three.dvd_of_dvd_pow at qm
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three qpr] at qm
      symm; exact qm
  -- Take modulo $5$ on both sides of heq, then apply sqmod5 to $p$ and $r$
    simp [qm] at heq; replace heq' := heq; apply_fun fun t => t % 5 at heq'; simp [Nat.add_mod] at heq'
    rw [Nat.mod_mod, show p^4 = (p^2)^2 by ring, Nat.mul_mod, Nat.pow_mod] at heq'
    nth_rw 2 [Nat.mul_mod] at heq'
  -- Check all possible cases and the only possibility left is $p=5$
    rcases sqmod5 p with pm|pm|pm <;> rcases sqmod5 r with rm'|rm'|rm'; any_goals simp [pm, rm'] at heq'
    replace pm : p = 5 := by
      rw [← Nat.dvd_iff_mod_eq_zero] at pm; apply Nat.prime_five.dvd_of_dvd_pow at pm
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_five ppr] at pm
      symm; exact pm
  -- Plug in $p=5$ and $q=3$ to heq, then solve for $r=19$
    simp [pm, ← Nat.sub_eq_iff_eq_add'] at heq; rw [show 1444 = 4 * 19^2 by simp] at heq
    apply mul_left_cancel₀ at heq; rw [pow_left_inj₀] at heq; split_ands; any_goals linarith
    apply le_of_lt; rw [← Nat.sub_pos_iff_lt, heq]; simp
-- Conversely, it is straightforward to check that $p=5$, $q=3$ and $r=19$ is a solution to the equation in question
  rintro ⟨_,_,_⟩; simp_all