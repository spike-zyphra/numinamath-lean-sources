import Mathlib

open Real
/--
Problem statement (Main theorem of this file):
5. If the real number $k$ makes the equation about $x$
$$
\left(x^{2}-1\right)\left(k x^{2}-6 x-8\right)=0
$$

have exactly three distinct real roots, then $k$ is called a "good number". The number of such good numbers $k$ is ( ) .
(A) 1
(B) 2
(C) 3
(D) 4

Solution:
5. D.

From the condition, we know that $x= \pm 1$ are roots of the equation. If $x=1$ is a root of the equation $$ k x^{2}-6 x-8=0 $$

we get $k=14$, and the other root is $-\frac{4}{7}$, which satisfies the condition. If $x=-1$ is a root of equation (1), we get $k=2$, and the other root is -4, which satisfies the condition. If $x= \pm 1$ are not roots of equation (1): When $k=0$, the roots of equation (1) are $-\frac{4}{3}$, which satisfies the condition; When $k \neq 0$, the discriminant of equation (1) is $$ \Delta=(-6)^{2}+32 k=0 \Rightarrow k=-\frac{9}{8} \text {. } $$

In this case, equation (1) has two equal real roots $-\frac{8}{3}$, which satisfies the condition. Therefore, there are 4 good values of $k$.
-/


theorem algebra_313276 :
  {k : ℝ | {x : ℝ | (x^2 - 1) * (k * x^2 - 6 * x - 8) = 0}.encard = 3}.ncard = 4 := by
  have h_set: {k : ℝ | {x : ℝ | (x^2 - 1) * (k * x^2 - 6 * x - 8) = 0}.encard = 3} = {0,-9/8,2,14} := by
    ext k
    simp only [Set.mem_setOf_eq]

    constructor
    . intro h_sol_three
      simp
      by_cases hk1: k = 0
      . left; assumption
      . right
        by_cases hk2: k < -9/8
        . have : {x | (x ^ 2 - 1) * (k * x ^ 2 - 6 * x - 8) = 0} = {1,-1} := by
            ext x
            simp only [Set.mem_setOf_eq]
            constructor
            . intro h
              simp at h
              cases' h with h1 h2
              . rw [(by ring: x^2-1 = (x-1)*(x+1))] at h1
                simp at h1
                simp
                cases h1
                . left; linarith
                . right; linarith
              . have : k * x ^ 2 - 6 * x - 8 = k * (x - 3 / k)^2 - 8 - 9 / k := by
                  ring_nf
                  field_simp
                  ring_nf

                rw [this] at h2
                have : (x - 3 / k) ^ 2 ≥ 0 := by positivity
                have : - 8 - 9 / k < 0 := by
                  have : 8 * k < -9 := by linarith
                  rw [mul_comm] at this
                  rw [← div_lt_iff_of_neg' (by nlinarith)] at this
                  rw [← neg_div'] at this
                  linarith
                nlinarith

            . intro h
              simp at h
              cases' h with h1 h2
              . rw [h1]; linarith
              . rw [h2]; linarith
          rw [this] at h_sol_three
          rw [Set.encard_pair (by linarith)] at h_sol_three
          contradiction

        . by_cases hk3: k=-9/8
          . left; assumption
          . right
            have hk4: k > - 9 / 8 := by
              simp at hk2
              exact lt_of_le_of_ne hk2 (Ne.symm hk3)

            have : {x | (x ^ 2 - 1) * (k * x ^ 2 - 6 * x - 8) = 0} = {1,-1, (3 - sqrt (9 + 8 * k))/k, (3 + sqrt (9 + 8 * k))/k} := by
              ext x
              simp only [Set.mem_setOf_eq]
              simp
              constructor
              . intro h
                cases' h with h1 h2
                . rw [(by ring: x^2-1 = (x-1)*(x+1))] at h1
                  simp at h1
                  cases h1
                  . left; linarith
                  . right; left; linarith
                . right; right
                  have : k * x ^ 2 - 6 * x - 8 = k * (x - (3 - sqrt (9 + 8 * k)) / k) * (x - (3 + sqrt (9 + 8 * k)) / k) := by
                    ring_nf
                    field_simp
                    rw [sq_sqrt (by linarith)]
                    ring_nf

                  rw [this] at h2
                  simp at h2
                  cases' h2 with h21 h22
                  . left
                    cases h21
                    . contradiction
                    . linarith
                  . right
                    linarith

              . intro h
                rcases h with rfl | rfl | rfl | rfl
                . ring_nf; simp;
                . ring_nf; simp;
                . right
                  ring_nf
                  field_simp
                  rw [sq_sqrt (by linarith)]
                  ring_nf

                . right
                  ring_nf
                  field_simp
                  rw [sq_sqrt (by linarith)]
                  ring_nf

            rw [this] at h_sol_three


            by_contra h_neg
            push_neg at h_neg
            rcases h_neg with ⟨h_neg1, h_neg2⟩

            rw [Set.encard_insert_of_not_mem] at h_sol_three
            rw [Set.encard_insert_of_not_mem] at h_sol_three

            have : (3 - √(9 + 8 * k)) / k ≠ (3 + √(9 + 8 * k)) / k := by
              by_contra h
              field_simp at h
              have : √(9 + 8 * k) = 0:= by linarith
              rw [sqrt_eq_zero'] at this
              linarith

            rw [Set.encard_pair this] at h_sol_three
            ring_nf at h_sol_three
            contradiction

            -- ⊢ -1 ∉ {(3 - √(9 + 8 * k)) / k, (3 + √(9 + 8 * k)) / k}
            simp
            constructor
            . by_contra h
              field_simp at h
              have : 3 + k = √(9 + 8 * k):= by linarith
              have : (3 + k)^2 = 9 + 8 * k:= by rw [this, sq_sqrt (by linarith)]
              ring_nf at this
              have : k * (k - 2) = 0:= by linarith
              simp at this
              cases this
              . contradiction
              . have : k = 2 := by linarith
                contradiction
            . by_contra h
              field_simp at h
              have : -3 - k = √(9 + 8 * k):= by linarith
              have : (-3 - k)^2 = 9 + 8 * k:= by rw [this, sq_sqrt (by linarith)]
              ring_nf at this
              have : k * (k - 2) = 0:= by linarith
              simp at this
              cases this
              . contradiction
              . have : k = 2 := by linarith
                contradiction

            -- ⊢ 1 ∉ {-1, (3 - √(9 + 8 * k)) / k, (3 + √(9 + 8 * k)) / k}
            simp
            constructor
            . linarith
            . constructor
              . by_contra h
                field_simp at h
                have : 3 - k = √(9 + 8 * k):= by linarith
                have : (3 - k)^2 = 9 + 8 * k:= by rw [this, sq_sqrt (by linarith)]
                ring_nf at this
                have : k * (k - 14) = 0:= by linarith
                simp at this
                cases this
                . contradiction
                . have : k = 14 := by linarith
                  contradiction

              . by_contra h
                field_simp at h
                have : k - 3 = √(9 + 8 * k):= by linarith
                have : (k - 3)^2 = 9 + 8 * k:= by rw [this, sq_sqrt (by linarith)]
                ring_nf at this
                have : k * (k - 14) = 0:= by linarith
                simp at this
                cases this
                . contradiction
                . have : k = 14 := by linarith
                  contradiction

    . intro hk
      rw [Set.encard_eq_three]
      rcases hk with rfl | rfl | rfl | rfl
      . use 1, -1, -4 / 3
        constructor
        . linarith
        . constructor
          . linarith
          . constructor
            . linarith
            . simp
              ext x
              simp only [Set.mem_setOf_eq]
              constructor
              . intro h
                simp at h
                simp
                cases' h with h1 h2
                . have : x = 1 ∨ x = -1 := by
                    rw [(by ring: x^2-1 = (x-1)*(x+1))] at h1
                    simp at h1
                    cases h1
                    . left; linarith
                    . right; linarith
                  cases this
                  . left; assumption
                  . right; left; assumption
                . right; right; linarith
              . intro h
                rcases h with rfl | rfl | rfl
                . left; linarith
                . left; linarith
                . right; linarith

      . use 1, -1, -8 / 3
        constructor
        . linarith
        . constructor
          . linarith
          . constructor
            . linarith
            . simp
              ext x
              simp only [Set.mem_setOf_eq]
              constructor
              . intro h
                simp
                cases' h with h1 h2
                . -- x = 1 ∨ x = -1 := by
                  rw [(by ring: x^2-1 = (x-1)*(x+1))] at h1
                  simp at h1
                  cases h1
                  . left; linarith
                  . right; left; linarith
                . right; right
                  have : -9/8*x^2 - 6*x - 8 = -(9/8) * (x + 8/3)^2 := by ring
                  rw [this] at h2
                  have : (x + 8 / 3) * (x + 8 / 3) = 0 := by linarith
                  simp at this
                  linarith
              . intro h
                rcases h with rfl | rfl | rfl
                . left; linarith
                . left; linarith
                . right; linarith
      . use 1, -1, 4
        constructor
        . linarith
        . constructor
          . linarith
          . constructor
            . linarith
            . simp
              ext x
              simp only [Set.mem_setOf_eq]
              constructor
              . intro h
                cases' h with h1 h2
                . rw [(by ring: x^2-1 = (x-1)*(x+1))] at h1
                  simp at h1
                  cases h1
                  . left; linarith
                  . right; left; linarith
                . right
                  have : 2 * x ^ 2 - 6 * x - 8 = 2 * (x + 1) * (x - 4) := by ring
                  rw [this] at h2
                  have : (x + 1) * (x - 4) = 0 := by linarith
                  simp at this
                  simp
                  cases this
                  . left; linarith
                  . right; linarith
              . intro h

                rcases h with rfl | rfl | rfl
                . left; linarith
                . left; linarith
                . right; linarith
      . use 1, -1, -(4/7)
        constructor
        . linarith
        . constructor
          . linarith
          . constructor
            . linarith
            . simp
              ext x
              simp only [Set.mem_setOf_eq]
              constructor
              . intro h
                cases' h with h1 h2
                . rw [(by ring: x^2-1 = (x-1)*(x+1))] at h1
                  simp at h1
                  cases h1
                  . left; linarith
                  . right; left; linarith
                . have : 14 * x ^ 2 - 6 * x - 8 = 14 * (x - 1) * (x + 4 / 7) := by ring
                  rw [this] at h2
                  have : (x - 1) * (x + 4 / 7) = 0 := by linarith
                  simp at this
                  simp
                  cases this
                  . left; linarith
                  . right; right; linarith
              . intro h
                rcases h with rfl | rfl | rfl
                . left; linarith
                . left; linarith
                . right; nlinarith

  rw [h_set]
  norm_num
