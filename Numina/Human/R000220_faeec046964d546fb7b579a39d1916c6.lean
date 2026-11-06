import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all pairs  $(p,\ q)$  of positive integers such that  $3p^3-p^2q-pq^2+3q^3=2013.$-/
theorem number_theory_8611 :
  {(p, q) : ℤ × ℤ | 0 < p ∧ 0 < q ∧ 3 * p^3 - p^2 * q - p * q^2 + 3 * q^3 = 2013} =
  {(2, 9), (9, 2)} := by
    ext x
    simp
    -- In this proof, `x.1` means $p$, `x.2` means $q$.
    set p := x.1 with hp
    set q := x.2 with hq
    constructor
    · intro ⟨ppos, qpos, c1⟩
      -- Rewrite the equation by factoring:
      --  \[
      --  3(p^3 + q^3) - pq(p + q) = 2013.
      --  \].
      -- Using the identity \(p^3 + q^3 = (p + q)(p^2 - pq + q^2)\), the equation becomes:
      -- \[
      -- (p + q)(3(p^2 - pq + q^2) - pq) = 2013.
      -- \]
      have c2 : 2013 = (p + q) * (3 * (p + q)^2 - 10 * p * q) := by nlinarith
      -- $pq \le {\left( {\frac{{p + q}}{2}} \right)^2}  \Rightarrow $
      -- ${p^3} - {p^2}q - p{q^2} + 3{q^3} = \left( {p + q} \right)\left[ {3{{\left( {p + q} \right)}^2} - 10pq} \right]$
      -- $\ge \left( {p + q} \right)\left[ {3{{\left( {p + q} \right)}^2} - 10{{\left( {\frac{{p + q}}{2}} \right)}^2}} \right] =
      -- \frac{1}{2}{\left( {p + q} \right)^3}$ therefore
      -- $\frac{1}{2}{\left( {p + q} \right)^3} \le 2013 \Rightarrow p + q \le 15$ ,
      have c3 : 2 * (p + q)^3 ≤ 2013 * 4 := by
        calc
          _ = (p + q) * (12 * (p + q)^2 - 10 * (p + q)^2 ) := by nlinarith
          _ ≤ (p + q) * (12 * (p + q)^2 - 40 * p * q) := by
            refine Int.mul_le_mul le_rfl ?_ (by
              simp; exact Int.mul_le_mul (by omega) le_rfl (by nlinarith) (by simp)) (by omega)
            apply Int.sub_le_sub_left
            have : 4 * p * q ≤ (p + q)^2 := by
              ring_nf
              linarith [two_mul_le_add_sq p q ]
            linarith
          _ = _ := by nlinarith
      have c4 : p + q ≤ 15 := by nlinarith
      -- Factorize 2013 : \[
      -- 2013 = 3 \times 11 \times 61.
      -- \]
      have h1 : p + q ∣ 3 * 11 * 61 :=
        Dvd.intro (3 * (p + q) ^ 2 - 10 * p * q) (id (Eq.symm c2))
      -- Under the giving condition, $p + q$ can only be 11.
      have h2 : p + q = 11 := by
        have : p + q ≠ 1 := by omega
        have : p + q ≠ 3 := by
          intro h
          have : p < 3 := by omega
          have : q < 3 := by omega
          nlinarith
        have : 0 < p + q := by positivity
        interval_cases (p + q) <;> tauto
      simp [h2] at c2
      -- f  $p + q = 11 \Rightarrow pq = 18 \Rightarrow \left( {p,q} \right) = \left( {2,9} \right) $
      -- or  $(9,2)$ .
      have c5 : p * q = 18 := by nlinarith
      have : p = 2 ∧ q = 9 ∨ p = 9 ∧ q = 2 := by
        have : p ≤ 11 := by omega
        have : q = 11 - p := by omega
        interval_cases p <;> simp at this <;> simp [this] at c5 <;> tauto
      rcases this with hl | hr
      · left; ext <;> simp [←hp, ←hq] <;> tauto
      · right; ext <;> simp [←hp, ←hq] <;> tauto
    · -- Verify that \left( {p,q} \right) = \left( {2,9} \right) $ or  $(9,2)$ satisfy the condition.
      intro h
      rcases h with h | h <;> simp [Prod.eq_iff_fst_eq_snd_eq, ←hp, ←hq] at h <;> simp [h]
