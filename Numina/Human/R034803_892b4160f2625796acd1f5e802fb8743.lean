import Mathlib
set_option maxRecDepth 4000

open Finset Classical

/-Let $\lfloor x\rfloor$ denote the greatest integer less than or equal to $x$. How many positive integers less than 2005 can be expressed in the form $\lfloor x\lfloor x\rfloor\rfloor$ for some positive real $x$ ?-/
theorem number_theory_611345 : #{n ∈ Ico 1 2005 | ∃ x : ℝ, 0 < x ∧ n = ⌊x * ⌊x⌋₊⌋₊} = 990 := by
-- Define a function $f(x,y)$ to be $x^2+y$
  let f : ℕ × ℕ → ℕ := fun (x, y) => x ^ 2 + y
-- Prove that the set in question is equal to the image set of pairs (x, y) in $[1, 44] × [0, 45]$ with $$y< x$
  have fimg : image f ({P ∈ Icc 1 44 ×ˢ range 45 | P.2 < P.1}) =
  {n ∈ Ico 1 2005 | ∃ x : ℝ, 0 < x ∧ n = ⌊x * ⌊x⌋₊⌋₊} := by
  -- Rewrite the goal to a membership form and split `iff`
    simp [Finset.ext_iff, f, and_assoc]; intro n; constructor
    -- Introduce variables $a$ and $b$ with certain properties
    · rintro ⟨a, age, ale, b, _, blt, hab⟩; split_ands
      · suffices : 1 ^ 2 ≤ a ^ 2; omega
        gcongr
      · rw [← hab]; calc
          _ ≤ 44 ^ 2 + a := by gcongr
          _ ≤ 44 ^ 2 + 44 := by gcongr
          _ < _ := by norm_num
    -- Fulfill the goal with $b / a + a$ and check it satisfies the desired properties
      use b / a + a; constructor
      · positivity
      rw [Nat.floor_add_nat]; nth_rw 2 [Nat.floor_eq_zero.mpr]
      field_simp; norm_cast
      rw [Nat.floor_natCast, ← hab]; ring
      rw [div_lt_iff₀, one_mul]; norm_cast
      all_goals positivity
  -- Conversely, suppose we have a number $n$ of the form $⌊x * ⌊x⌋₊⌋₊$
    rintro ⟨nge, nltm, ⟨x, xpos, hx⟩⟩
    nth_rw 1 [← Int.floor_add_fract x] at hx
    rw [add_mul] at hx; have : ⌊x⌋ = ⌊x⌋₊ := by
      rw [← Int.floor_toNat, Int.toNat_of_nonneg]
      rw [Int.le_floor]; simp; positivity
    rw [this] at hx; norm_cast at hx
    rw [add_comm, Nat.floor_add_nat, ← pow_two] at hx
    have flle : ⌊x⌋₊ ≤ 44 := by
      rw [← Nat.lt_add_one_iff]; norm_num
      rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by simp)]
      omega
  -- Fulfill the goal with $⌊x⌋₊$ and $⌊Int.fract x * ↑⌊x⌋₊⌋₊$, then check they satisfy the desired properties
    use ⌊x⌋₊; split_ands
    · by_contra!; rw [Nat.lt_one_iff] at this
      simp [this] at hx; omega
    · exact flle
    use ⌊Int.fract x * ↑⌊x⌋₊⌋₊; split_ands
    · calc
        _ ≤ ⌊(1 : ℝ) * ⌊x⌋₊⌋₊ := by
          apply Nat.floor_le_floor; gcongr
          linarith only [Int.fract_lt_one x]
        _ < _ := by rw [one_mul, Nat.floor_natCast]; omega
    · rw [Nat.floor_lt, mul_lt_iff_lt_one_left]
      exact Int.fract_lt_one x
      · by_contra!; norm_cast at this
        rw [Nat.le_zero] at this; simp [this] at hx
        omega
      apply mul_nonneg; apply Int.fract_nonneg
      positivity
    · rw [hx]; ring
    apply mul_nonneg; apply Int.fract_nonneg
    positivity
-- Prove that $f$ is injective on the set of pairs (x, y) in $[1, 44] × [0, 45]$ with $$y< x$
  have finj : Set.InjOn f (filter (fun P => P.2 < P.1) (Icc 1 44 ×ˢ range 45)) := by
    rintro ⟨x, y⟩; simp [f]; intro xge xle _ ylt
    intro x' y' x'ge x'le _ y'lt heq
    by_contra!; by_cases h : x = x'
    · rw [h, add_left_cancel_iff] at heq
      specialize this h; contradiction
    rw [← ne_eq, ne_iff_lt_or_gt] at h
    rcases h with h|h
    · have : x ^ 2 < x' ^ 2 := by gcongr
      symm at heq; rw [← Nat.sub_eq_iff_eq_add'] at heq
      rw [Nat.sub_add_comm, Nat.sq_sub_sq] at heq
      suffices : y < (x' + x) * (x' - x) + y'; omega
      calc
        _ = (0 + y) * 1 + 0 := by simp
        _ ≤ (0 + y) * (x' - x) + y' := by gcongr; all_goals omega
        _ < _ := by gcongr; all_goals omega
      all_goals omega
    have : x' ^ 2 < x ^ 2 := by gcongr
    rw [← Nat.sub_eq_iff_eq_add'] at heq
    rw [Nat.sub_add_comm, Nat.sq_sub_sq] at heq
    suffices : y' < (x + x') * (x - x') + y; omega
    calc
      _ = (y' + 0) * 1 + 0 := by simp
      _ ≤ (y' + 0) * (x - x') + y := by gcongr; all_goals omega
      _ < _ := by gcongr; all_goals omega
    all_goals omega
-- Use `card_image_of_injOn` and `decide` to finish the goal
  rw [← fimg, card_image_of_injOn finj]; decide