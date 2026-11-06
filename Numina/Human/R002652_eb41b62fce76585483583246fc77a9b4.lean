import Mathlib
open Real

/-
The solutions to the system of equations
$log_{225} x + log_64 y = 4$
$log_x 225 - log_y 64 = 1$
are $(x_1,y_1)$ and $(x_2, y_2)$, Find $log_{30}(x_1y_1x_2y_2) = 12$
-/
theorem AIME_Algebra_718
  (e1 e2 : ℝ → ℝ → Prop)
  (hE1 : ∀ x y, e1 x y = (logb 225 x + logb 64 y = 4))
  (hE2 : ∀ x y, e2 x y = (logb x 225 - logb y 64 = 1))
  (roots : Finset (ℝ × ℝ))
  (hRoot : roots = {r : ℝ × ℝ | r.1 > 0 ∧ r.1 ≠ 1  ∧ r.2 > 0 ∧ r.2 ≠ 1 ∧ e1 r.1 r.2 ∧ e2 r.1 r.2})
  : roots.card = 2 ∧ (∀ (r1 r2 : roots) (_ : r1 ≠ r2), logb 30 (r1.1.1 * r1.1.2 * r2.1.1 * r2.1.2) = 12) := by
  /-
  Let $A = log_⁡225 x$ and let $B = log_64 y$
  -/
  let A x := logb 225 x
  let B y := logb 64 y
  have hA: ∀ x, A x = logb 225 x := by simp only [implies_true]
  have hB: ∀ y, B y = logb 64 y := by simp only [implies_true]
  /-
  From the first equation: $A + B = 4 ↔ B = 4 − A$
  -/
  have derive_1 x y : e1 x y ↔ B y = 4 - A x := by
    rw [hE1]
    unfold A B
    exact Iff.symm eq_sub_iff_add_eq'
  /-
  Plugging this into the second equation yields $\frac1A − \frac1B = 1$
  -/
  have derive_2 x y : e2 x y ↔ 1 / A x - 1 / B y = 1 := by
    rw [hE2]
    unfold A B
    unfold logb
    rw [one_div_div, one_div_div]
  /-
  So the system is rewrite as $B = 4 − A$ and $\frac1A − \frac1B = 1$
  -/
  have derive_3 x y : e1 x y ∧ e2 x y ↔ (B y = 4 - A x) ∧ ((1 / A x) - (1 / (4 - A x))) = 1 := by
    rw [derive_1, derive_2]
    simp only [one_div, and_congr_right_iff]
    intro h
    rw [h]
  /-
  When $B$ is not zero, the second equation can be rewritted as $A ^ 2 - 6 A + 4 = 0$
  -/
  have derive_4 x (hx : x ≠ 1 ∧ x > 0) (hy : (4 - A x) ≠ 0)
    : (1 / A x) - (1 / (4 - A x)) = 1 ↔ A x ^ 2 - 6 * A x + 4 = 0 := by
    have Ax_ne_0 : A x ≠ 0 := by
      unfold A logb
      apply div_ne_zero
      apply Real.log_ne_zero_of_pos_of_ne_one
      exact hx.2
      exact hx.1
      apply Real.log_ne_zero_of_pos_of_ne_one
      . simp only [Nat.ofNat_pos]
      . simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    calc (1 / A x) - (1 / (4 - A x)) = 1
      _ ↔ (1 / A x) + (- (1 / (4 - A x))) = 1 := by exact Eq.congr_right rfl
      _ ↔ A x * ((1 / A x) + (- (1 / (4 - A x)))) = A x * 1 := by
        refine Iff.symm (IsUnit.mul_right_inj ?_)
        apply IsUnit.mk0
        exact Ax_ne_0
      _ ↔ (4 - A x) * (A x * ((1 / A x) + (- (1 / (4 - A x))))) = (4 - A x) * (A x * 1) := by
        refine Iff.symm (IsUnit.mul_right_inj ?_)
        apply IsUnit.mk0
        exact hy
      _ ↔ (4 - A x) * (1 + A x * (- (1 / (4 - A x)))) = (4 - A x) * (A x * 1) := by
        rw [Distrib.left_distrib]
        rw [mul_one_div_cancel Ax_ne_0]
      _ ↔  ((4 - A x) * 1 + (4 - A x) * (A x * (- (1 / (4 - A x))))) = (4 - A x) * (A x * 1) := by
        rw [Distrib.left_distrib]
      _ ↔ _ := by
        have : (4 - A x) * (A x * (- (1 / (4 - A x)))) = -1 * A x := by
          set Bx := 4 - A x
          rw [neg_eq_neg_one_mul, ← mul_assoc, ← mul_mul_mul_comm, mul_comm Bx, ← mul_mul_mul_comm]
          rw [(by exact mul_one_div_cancel hy  : Bx * (1 / Bx) = 1)]
          simp only [neg_mul, one_mul, mul_one]
        rw [this]
      _ ↔ (4 - A x) * 1 + -1 * A x - (4 - A x) * (A x * 1) = 0 := by
        exact Iff.symm sub_eq_zero
      _ ↔ A x ^ 2 - 6 * A x + 4 = 0 := by
        group
  /-
  By the root finding formula for quadratic equation, the solution of such an equation is either
  $3 + \sqrt 5$ or $3 - \sqrt 5$
  -/
  have derive_5 x : x ^ 2 - 6 * x + 4 = 0 ↔ x = 3 + sqrt 5 ∨ x = 3 - sqrt 5:= by
    have : x ^ 2 - 6 * x = x ^ 2 + (-6) * x := by
      simp only [eq_iff_iff, one_div, implies_true, and_congr_right_iff, ne_eq, gt_iff_lt, and_imp, neg_mul, B, A]
      rfl
    rw [this, pow_two, (by exact Eq.symm (one_mul (x * x)): x * x = 1 * (x * x))]
    let d := @discrim _ (inferInstance: Ring ℝ) 1 (-6) 4
    let hD1 : d = @discrim _ (inferInstance: Ring ℝ) 1 (-6) 4 := by unfold d;rfl
    let nat_4_4_le_6_6 : 4 * 4 ≤ 6 * 6 := by linarith
    let hD2 : d = 20 := by unfold d discrim; linarith
    let s := sqrt d
    have s_pos : s > 0 := by unfold s;refine sqrt_pos_of_pos ?_;rw [hD2];simp
    have hS1 : s * s = 20 := by
      unfold s
      refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mp (congrArg sqrt (id (Eq.symm hD2)))
      refine sqrt_pos_of_pos ?_
      rw [hD2]
      simp only [Nat.ofNat_pos]
    have hS2 : s = 2 * √5 := by
      refine (sqrt_eq_iff_eq_sq ?_ ?_).mpr ?_
      . rw[hD2]; simp only [Nat.ofNat_nonneg]
      . simp
      . rw[hD2, pow_two, ← mul_assoc]
        symm
        ring_nf
        simp only [Nat.ofNat_nonneg, sq_sqrt]
        ring_nf
    calc _
      _ ↔ x = (-(-6) + s) / (2 * 1) ∨ x = (-(-6) - s) / (2 * 1) := by
        apply quadratic_eq_zero_iff
        . simp only [ne_eq, one_ne_zero, not_false_eq_true]
        rw [← hD1, hS1, ← hD2]
      _ ↔ _ := by
        rw [hS2]
        simp only [neg_neg, mul_one]
        have : (6 : ℝ) = 2 * 3 := by linarith
        rw [this]
        rw [← mul_add, ← mul_sub]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
  have derive_6 x (hx : x ≠ 1 ∧ x > 0) (hy : (4 - A x) ≠ 0) :
    (1 / A x) - (1 / (4 - A x)) = 1  ↔ A x = 3 + sqrt 5 ∨ A x = 3 - sqrt 5 := by
    rw [derive_4, ← derive_5]
    exact hx
    exact hy

  /-
  So when $4 − A ≠ 0$ $A = 3 + \sqrt 5$ or $A = 3 - \sqrt 5$
  -/
  have derive_7 x y (hx : x ≠ 1 ∧ x > 0) (hy : (4 - A x) ≠ 0)
    : e1 x y ∧ e2 x y ↔  ((A x = 3 + sqrt 5 ∧ B y = 1 - sqrt 5)) ∨ ((A x = 3 - sqrt 5) ∧ B y = 1 + sqrt 5) := by
      have : e1 x y ∧ e2 x y ↔  (B y = 4 - A x) ∧ (A x = 3 + sqrt 5 ∨ A x = 3 - sqrt 5) := by
        rw [derive_3, derive_6]
        exact hx
        exact hy
      rw [this]
      constructor
      . intro h
        rw [and_or_left] at h
        cases' h with ha hb
        let ⟨hl, hr⟩ := ha
        left
        rw [hr, hl, hr]
        group
        rw [and_true]
        trivial
        let ⟨hl, hr⟩ := hb
        rw [hr, hl, hr]
        group
        right
        trivial
      . intro h
        rw [and_or_left]
        cases' h with ha hb
        left
        let ⟨hl, hr⟩ := ha
        rw [← hl, hl, hr]
        group
        rw [and_true]
        trivial
        let ⟨hl, hr⟩ := hb
        rw [hr, hl]
        group
        right
        trivial

  /-
  And $A = 3 + \sqrt 5$ or $A = 3 - \sqrt 5$
  means $x = 255 ^ {3 + \sqrt 5}, y = 64 ^ {1 - \sqrt 5}$ or $x = 255 ^ {3 - \sqrt 5}, y = 64 ^ {1 + \sqrt 5}$
  -/
  have derive_8 x y (hx : x ≠ 1 ∧ x > 0) (hy : y ≠ 1 ∧ y > 0) :
    ((A x = 3 + sqrt 5 ∧ B y = 1 - sqrt 5)) ∨ ((A x = 3 - sqrt 5) ∧ B y = 1 + sqrt 5) ↔
    (x = 225 ^ (3 + sqrt 5) ∧ y = 64 ^ (1 - sqrt 5)) ∨ (x = 225 ^ (3 - sqrt 5) ∧ y = 64 ^ (1 + sqrt 5)) := by
      have : A x = 3 + sqrt 5 ↔ x = 225 ^ (3 + sqrt 5) := by
        unfold A
        constructor
        . intro h; rw [← h]; rw [rpow_logb];simp only [Nat.ofNat_pos];simp only [ne_eq,
          OfNat.ofNat_ne_one, not_false_eq_true];exact hx.2
        . intro h; rw [h]; rw [logb_rpow];simp only [Nat.ofNat_pos];simp only [ne_eq,
          OfNat.ofNat_ne_one, not_false_eq_true];
      rw [this]
      have : A x = 3 - sqrt 5 ↔ x = 225 ^ (3 - sqrt 5) := by
        unfold A
        constructor
        . intro h; rw [← h]; rw [rpow_logb];simp only [Nat.ofNat_pos];simp only [ne_eq,
          OfNat.ofNat_ne_one, not_false_eq_true];exact hx.2
        . intro h; rw [h]; rw [logb_rpow];simp only [Nat.ofNat_pos];simp only [ne_eq,
          OfNat.ofNat_ne_one, not_false_eq_true];
      rw [this]
      have : B y = 1 - sqrt 5 ↔ y = 64 ^ (1 - sqrt 5) := by
        unfold B
        constructor
        . intro h; rw [← h]; rw [rpow_logb];simp only [Nat.ofNat_pos];simp only [ne_eq,
          OfNat.ofNat_ne_one, not_false_eq_true];exact hy.2
        . intro h; rw [h]; rw [logb_rpow];simp only [Nat.ofNat_pos];simp only [ne_eq,
          OfNat.ofNat_ne_one, not_false_eq_true];
      rw [this]
      have : B y = 1 + sqrt 5 ↔ y = 64 ^ (1 + sqrt 5) := by
        unfold B
        constructor
        . intro h; rw [← h]; rw [rpow_logb];simp only [Nat.ofNat_pos];simp only [ne_eq,
          OfNat.ofNat_ne_one, not_false_eq_true];exact hy.2
        . intro h; rw [h]; rw [logb_rpow];simp only [Nat.ofNat_pos];simp only [ne_eq,
          OfNat.ofNat_ne_one, not_false_eq_true];
      rw [this]

  /-
  So when $4 - A ≠ 0$
  $x = 255 ^ {3 + \sqrt 5}, y = 64 ^ {1 - \sqrt 5}$ or $x = 255 ^ {3 - \sqrt 5}, y = 64 ^ {1 + \sqrt 5}$
  -/
  have derive_9 x y (hx : x ≠ 1 ∧ x > 0) (hy : y ≠ 1 ∧ y > 0) (hy' : (4 - A x) ≠ 0):
    e1 x y ∧ e2 x y ↔ (x = 225 ^ (3 + sqrt 5) ∧ y = 64 ^ (1 - sqrt 5)) ∨ (x = 225 ^ (3 - sqrt 5) ∧ y = 64 ^ (1 + sqrt 5)) := by
    rw [derive_7 x y hx hy', derive_8 x y hx hy]

  have hRoot1 r : r ∈ roots ↔ r.1 > 0 ∧ r.1 ≠ 1 ∧ r.2 > 0 ∧ r.2 ≠ 1 ∧ e1 r.1 r.2 ∧ e2 r.1 r.2 := by exact Eq.to_iff (congrFun hRoot r)

  /-
  Using these results, we conclude that the set $\{(r : ℝ × ℝ) | (r\ is\ a\ root) ∧ 4 - A(r.1) ≠ 0\}$ is
  $\{(r : ℝ × ℝ) | (r.1 = 255 ^ {3 + \sqrt 5} ∧ r.2 = 64 ^ {1 - \sqrt 5}) ∨ (r.1 = 255 ^ {3 - \sqrt 5} ∨  r.2 = 64 ^ {1 + \sqrt 5)}\}$
  whose cardinality is two
  -/
  have root_card (s : Finset (ℝ × ℝ)) (hS : s.toSet = {(r : ℝ × ℝ) | (r ∈ roots) ∧ (4 - A r.1) ≠ 0}) :
    s.card = 2 ∧ (↑s = {(x : ℝ × ℝ)| x.1 = 225 ^ (3 + √5) ∧ x.2 = 64 ^ (1 - √5) ∨ x.1 = 225 ^ (3 - √5) ∧ x.2 = 64 ^ (1 + √5)}) := by
    have ht x y (h : ((((4 - A x ≠ 0 ∧ x > 0) ∧ x ≠ 1) ∧ y > 0) ∧ y ≠ 1)) :
      e1 x y ∧ e2 x y ↔ (x = 225 ^ (3 + sqrt 5) ∧ y = 64 ^ (1 - sqrt 5)) ∨ (x = 225 ^ (3 - sqrt 5) ∧ y = 64 ^ (1 + sqrt 5))
      := derive_9 x y (And.intro h.1.1.2 h.1.1.1.2)  (And.intro h.2 h.1.2)  (h.1.1.1.1)
    /-
    First we rewriting the (r is a root) part of the set using previous results
    After this, there are still some redundancy condition in the defination of the set
    -/
    conv at hS =>
      arg 2
      arg 1
      simp only
      rw [((Set.eqOn_univ _ _).mp (fun x hx => congrArg (·∧ (4 - A x.1 ≠ 0)) (iff_iff_eq.mp (hRoot1 x))))]
      intro x
      rw [and_comm, ← and_assoc, ← and_assoc, ← and_assoc, ← and_assoc]
      rw [and_congr_right (ht x.1 x.2)]

    /-
    A bunch of helper results used to simplify the set.
    -/

    have h1: 3 + √5 > 0 := by
      calc 3 + √5
        _ > 3 := by
          have : √5 > 0 := by refine sqrt_pos_of_pos ?_; simp only [Nat.ofNat_pos]
          exact lt_add_of_pos_right 3 this
        _ > 0 := by simp only [Nat.ofNat_pos]

    have h2: (225: ℝ) ^ (3 + √5) > 0 := by
      apply Real.rpow_pos_of_pos
      simp only [Nat.ofNat_pos]

    have h3: (225: ℝ) ^ (3 + √5) ≠ 1 := by
      by_contra h
      have : (1 : ℝ) = 225 ^ (0 : ℝ) := by exact Eq.symm (rpow_zero 225)
      rw [this] at h
      apply (congrArg (logb 225 ·)) at h
      repeat rw [logb_rpow] at h
      rw [h] at h1
      exact (lt_self_iff_false 0).mp h1
      . simp only [Nat.ofNat_pos]
      . simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
      . simp only [Nat.ofNat_pos]
      . simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]

    have h4:  (64 : ℝ) ^ (1 - √5) > 0 :=  by
      apply Real.rpow_pos_of_pos
      simp only [Nat.ofNat_pos]

    have one_ne_five (h : (1 :ℝ) = 5) : False := by
      suffices g : ((1 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) from by (
        simp only [Nat.cast_one, Nat.cast_ofNat, OfNat.one_ne_ofNat] at g
      )
      have h1: (1 : ℝ) = ((1 : ℕ) : ℝ) := by exact Eq.symm Nat.cast_one
      have h5: (5 : ℝ) = ((5 : ℕ) : ℝ) := by exact rfl
      rw [h1, h5] at h
      exact h

    have h5:  (64 : ℝ) ^ (1 - √5) ≠ 1 :=  by
      by_contra h
      have : (1 : ℝ) = 64 ^ (0 : ℝ) := by exact Eq.symm (rpow_zero 64)
      rw [this] at h
      apply (congrArg (logb 64 ·)) at h
      repeat rw [logb_rpow] at h
      apply (congrArg (· + √5)) at h
      group at h
      apply (congrArg (· ^ 2)) at h
      rw [sq_sqrt] at h
      group at h
      . exact one_ne_five h
      . simp only [Nat.ofNat_nonneg]
      . simp only [Nat.ofNat_pos]
      . exact Ne.symm (OfNat.one_ne_ofNat 64)
      . exact Nat.ofNat_pos'
      . exact Ne.symm (OfNat.one_ne_ofNat 64)

    have h6: (225: ℝ) ^ (3 - √5) > 0 := by
      apply Real.rpow_pos_of_pos
      simp only [Nat.ofNat_pos]

    have nine_not_five (h : (9 :ℝ) = 5) : False := by
      suffices g : ((9 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) from by (
        apply congrArg (· -4) at h
        simp only [sub_left_inj, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff] at h
      )
      have h1: (9 : ℝ) = ((9: ℕ) : ℝ) := by exact rfl
      have h5: (5 : ℝ) = ((5 : ℕ) : ℝ) := by exact rfl
      rw [h1, h5] at h
      exact h

    have h7: (225: ℝ) ^ (3 - √5) ≠ 1 := by
      by_contra h
      have : (1 : ℝ) = 225 ^ (0 : ℝ) := by exact Eq.symm (rpow_zero 225)
      rw [this] at h
      apply (congrArg (logb 225 ·)) at h
      repeat rw [logb_rpow] at h
      apply (congrArg (· + √5)) at h
      simp only [sub_add_cancel, zero_add] at h
      apply (congrArg (· ^ 2)) at h
      rw [sq_sqrt] at h
      group at h
      exact nine_not_five h
      . exact Nat.ofNat_nonneg' 5
      . exact Nat.ofNat_pos'
      . exact Ne.symm (OfNat.one_ne_ofNat 225)
      . exact Nat.ofNat_pos'
      . exact Ne.symm (OfNat.one_ne_ofNat 225)

    have h9: (64 : ℝ) ^ (1 + √5) > 0 := by
      apply Real.rpow_pos_of_pos
      simp only [Nat.ofNat_pos]


    have h15: 1 + √5 > 0 := by
      have h1: (1 : ℝ) > 0 := by exact Real.zero_lt_one
      have h2: √5 > 0 := by simp_all only [gt_iff_lt, zero_lt_one, Real.sqrt_pos, Nat.ofNat_pos]
      exact Right.add_pos' h1 h2

    have h10:  (64 : ℝ) ^ (1 + √5) ≠ 1 :=  by
      by_contra h
      have : (1 : ℝ) = 64 ^ (0 : ℝ) := by exact Eq.symm (rpow_zero 64)
      rw [this] at h
      apply (congrArg (logb 64 ·)) at h
      repeat rw [logb_rpow] at h
      simp only [rpow_zero] at h
      rw [h] at h15
      exact (lt_self_iff_false 0).mp h15
      . exact Nat.ofNat_pos'
      . exact Ne.symm (OfNat.one_ne_ofNat 64)
      . exact Nat.ofNat_pos'
      . exact Ne.symm (OfNat.one_ne_ofNat 64)

    have (a b : Prop) (h : a → b) : (b ∧ a) = a := by simp_all only [eq_iff_iff, one_div, gt_iff_lt, ne_eq,
      implies_true, and_congr_right_iff, and_imp, not_false_eq_true, and_self, Prod.forall, and_iff_right_iff_imp, B,
      A]

    /-
    Prove of they are really redundancy
    -/
    have tidy (x y : ℝ) : (((((4 - A x ≠ 0 ∧ x > 0) ∧ x ≠ 1) ∧ y > 0) ∧ y ≠ 1) ∧
      (x = 225 ^ (3 + √5) ∧ y = 64 ^ (1 - √5) ∨ x = 225 ^ (3 - √5) ∧ y = 64 ^ (1 + √5))) =
      ((x = 225 ^ (3 + √5) ∧ y = 64 ^ (1 - √5) ∨ x = 225 ^ (3 - √5) ∧ y = 64 ^ (1 + √5))) := by
        set a := (x = 225 ^ (3 + √5) ∧ y = 64 ^ (1 - √5) ∨ x = 225 ^ (3 - √5) ∧ y = 64 ^ (1 + √5))
        set b := ((((4 - A x ≠ 0 ∧ x > 0) ∧ x ≠ 1) ∧ y > 0) ∧ y ≠ 1)
        refine this a b ?_
        unfold a b
        intro h
        cases' h with h1 h2
        let ⟨hx, hy⟩ := h1
        rw [hx, hy]
        split_ands
        unfold A
        rw [logb_rpow]
        group
        . by_contra h
          apply congrArg (· + √5) at h
          group at h
          apply congrArg (· ^ 2) at h
          simp only [one_pow, Nat.ofNat_nonneg, sq_sqrt, OfNat.one_ne_ofNat] at h
        . simp only [Nat.ofNat_pos]
        . simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
        . exact h2
        . exact h3
        . exact h4
        . exact h5
        . unfold A
          rw [h2.1]
          rw [logb_rpow]
          group
          by_contra ha
          rw [ha] at h15
          exact (lt_self_iff_false 0).mp h15
          exact Nat.ofNat_pos'
          exact Ne.symm (OfNat.one_ne_ofNat 225)
        . rw [h2.1]
          exact h6
        . rw [h2.1]
          exact h7
        . rw [h2.2]
          exact h9
        . rw [h2.2]
          exact h10

    /-
    Remove the redundancy condition
    -/
    rw [((Set.eqOn_univ (fun x ↦ _) (fun x ↦ _)).mp (fun x hx => (tidy x.1 x.2)))] at hS

    /-
    Prove that this set has cardinality two
    -/
    let r1 : ℝ × ℝ := ⟨225 ^ (3 + √5), 64 ^ (1 - √5)⟩
    let r2 : ℝ × ℝ := ⟨225 ^ (3 - √5), 64 ^ (1 + √5)⟩
    constructor
    refine Finset.card_eq_two.mpr ?_
    use r1, r2
    constructor
    unfold r1 r2
    by_contra h
    simp only [Prod.mk.injEq] at h
    replace h := h.left
    apply (congrArg (logb 225 ·)) at h
    rw [logb_rpow, logb_rpow] at h
    apply (congrArg (3 - ·)) at h
    rw [← sub_add] at h
    group at h
    apply (congrArg (√5 + ·)) at h
    group at h
    have h1: (2 : ℝ) > 0 := by exact zero_lt_two
    have h2: √5 > 0 := by simp only [gt_iff_lt, Real.sqrt_pos, Nat.ofNat_pos]
    have h12: √5 * 2 > 0 := by simp only [gt_iff_lt, Real.sqrt_pos, Nat.ofNat_pos,
      mul_pos_iff_of_pos_left]
    rw [← h] at h12
    exact (lt_self_iff_false 0).mp h12
    exact Nat.ofNat_pos'
    exact Ne.symm (OfNat.one_ne_ofNat 225)
    exact Nat.ofNat_pos'
    exact Ne.symm (OfNat.one_ne_ofNat 225)
    rw [Finset.ext_iff]
    intro r
    rw [← Finset.mem_coe]
    rw [hS]
    unfold r1 r2
    simp only [Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
    have (x : ℝ × ℝ) (a b : ℝ): ((x.1 = a) ∧ (x.2 = b)) ↔ x = (a, b) := by
      obtain ⟨fst, snd⟩ := x
      simp_all only [Prod.mk.injEq]
    rw [this, this]
    exact hS
  /-
  Prove that for all root, $4 - A ≠ 0$
  -/
  have h4_min_Ax_not_zero (r : ℝ × ℝ) (hr : r ∈ roots) : ¬ 4 - A r.1 = 0 := by
    by_contra h
    rw [hRoot1] at hr
    unfold A at h
    have h1 := hr.2.2.2.2.1
    have h2 := hr.2.2.2.2.2
    rw [hE1] at h1
    rw [hE2] at h2
    apply (congr_arg (· + logb 225 r.1)) at h
    simp only [sub_add_cancel, zero_add] at h
    rw [h] at h1
    simp only [add_right_eq_self] at h1
    have : r.2 = 1 := by simp_all only [eq_iff_iff, one_div, gt_iff_lt, ne_eq, implies_true, and_congr_right_iff,
      and_imp, Prod.forall, add_zero, and_self, and_true, sub_self, inv_zero, sub_zero, inv_eq_one,
      OfNat.ofNat_ne_one, B, A]
    exact (hr.2.2.2.1 this).elim

  /-
  Together, we know the roots itself is equal to the previous set we defined and has cardinality two
  -/
  have ⟨hCard_is_2, hRoot3⟩ : roots.card = 2 ∧ (↑roots = {(x : ℝ×ℝ) | x.1 = 225 ^ (3 + √5) ∧ x.2 = 64 ^ (1 - √5) ∨ x.1 = 225 ^ (3 - √5) ∧ x.2 = 64 ^ (1 + √5)}) := by
    let div_roots := {(r : ℝ × ℝ) | (r ∈ roots) ∧ (4 - A r.1) ≠ 0}
    let other_roots := {(r : ℝ × ℝ) | (r ∈ roots) ∧ (4 - A r.1) = 0}
    have div_in : div_roots ⊆ roots := by
      exact Set.sep_subset (Membership.mem roots.val) fun x ↦ 4 - A x.1 ≠ 0
    have div_finite : Set.Finite div_roots := Set.Finite.subset (Finite.of_fintype roots) div_in
    obtain ⟨finite_div_set, hFD⟩ := Set.Finite.exists_finset_coe div_finite
    have hRoot: roots = div_roots ∪ other_roots := by
      ext x
      constructor
      intro hx
      rw [Set.mem_union, Set.mem_def, Set.mem_def]
      unfold div_roots other_roots
      conv =>
        left
        whnf
      rw [Classical.or_iff_not_imp_left]
      intro hp
      whnf at hp ⊢
      constructor
      . exact hx
      . contrapose hp
        simp only [ne_eq, imp_false, not_and, Decidable.not_not, Classical.not_imp]
        exact ⟨hx, hp⟩
      . rw [Set.mem_union]
        repeat rw [Set.mem_def]
        unfold div_roots other_roots
        intro ha
        cases' ha with x y
        whnf at x
        exact x.1
        whnf at y
        exact y.1
    have other_empty: other_roots = ∅ := by
      refine Set.eq_empty_of_forall_not_mem ?_
      intro x
      have {t : Type} x (s : Finset t) : (x ∈ s) = (x ∈ (s : Set t)) := rfl
      rw [Set.mem_def]
      unfold other_roots
      whnf
      intro h
      whnf at h
      let ⟨hl, hr⟩ := h
      apply (h4_min_Ax_not_zero _) at hl
      exact (hl hr)
    rw [other_empty, Set.union_empty] at hRoot
    rw [← hFD] at hRoot
    rw [Finset.coe_inj] at hRoot
    have := root_card finite_div_set hFD
    repeat rw [← hRoot] at this
    exact this

  constructor
  . exact hCard_is_2
  . intro r1 r2
  /-
  Now we calculate $log_{30}(x_1y_1x_2y_2)$
  -/
    let ⟨r1, hr1⟩ := r1
    let ⟨r2, hr2⟩ := r2
    intro hNe
    simp only [ne_eq, Subtype.mk.injEq] at hNe
    /-
    Prove that $255^{3 + \sqrt5} * (255^{3 - \sqrt5} = 15 ^ {12}$
    -/
    have hE1 :  ((225 : ℝ) ^ (3 + √5)) * 225 ^ (3 - √5) = 15 ^ (12:ℝ) := by
      rw [← rpow_add]
      ring_nf
      simp only [Nat.ofNat_pos]
    /-
    Prove that $64^{1 + \sqrt5} * 64^{1 - \sqrt5} = 2 ^ {12}$
    -/
    have hE2 :  ((64 : ℝ) ^ (1 + √5)) * 64 ^ (1 - √5) = 2 ^ (12:ℝ) := by
      rw [← rpow_add]
      ring_nf
      simp only [Nat.ofNat_pos]
    have hE3 : (15 : ℝ) * 2 = 30 := by ring_nf
    rw [← Finset.mem_coe] at hr1 hr2
    rw [hRoot3, Set.mem_def] at hr1 hr2
    /-
    Traverse all situations of choosing two value from the root set.
    For those don't fit the requirement of not equal, we conclude false to proof the goal.
    -/
    cases' hr1 with hr11 hr12
    . cases' hr2 with hr21 hr22
      . rw [← hr21.1, ← hr21.2, ← Prod.ext_iff] at hr11
        exact (hNe hr11).elim
      . rw [hr11.1, hr11.2, hr22.1, hr22.2]
        /-
        Prove that $log_{30}(x_1y_1x_2y_2) = 12$
        -/
        rw [mul_comm _ (225 ^ (3 - √5)), ← mul_assoc (225 ^ (3 - √5)) _]
        rw [mul_assoc, mul_comm (225 ^ (3 - √5)), mul_comm (64 ^ (1 - √5))]
        rw [hE1, hE2]
        rw [← mul_rpow, hE3, logb_rpow]
        simp only [Nat.ofNat_pos]
        simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
        simp only [Nat.ofNat_nonneg]
        simp only [Nat.ofNat_nonneg]
    . cases' hr2 with hr21 hr22
      . rw [hr21.1, hr21.2, hr12.1, hr12.2]
        /-
        Prove that $log_{30}(x_1y_1x_2y_2) = 12$
        -/
        rw [mul_assoc (225 ^ (3 - √5)), mul_comm (64 ^ (1 + √5))]
        rw [← mul_assoc (225 ^ (3 - √5)), mul_assoc]
        rw [mul_comm (225 ^ (3 - √5))]
        rw [hE1, hE2]
        rw [← mul_rpow, hE3, logb_rpow]
        simp only [Nat.ofNat_pos]
        simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
        simp only [Nat.ofNat_nonneg]
        simp only [Nat.ofNat_nonneg]
      . rw [← hr22.1, ← hr22.2, ← Prod.ext_iff] at hr12
        exact (hNe hr12).elim