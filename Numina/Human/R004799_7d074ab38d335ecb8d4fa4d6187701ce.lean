import Mathlib

open Classical Filter
open scoped Topology

/-- A lemma: for any `x : ℝ`, we have `⌊x⌋ + ⌊-x⌋ = 0` when `x ∈ ℤ`,
  and `⌊x⌋ + ⌊-x⌋ = -1` when `x ∉ ℤ`. -/
lemma add_floor_neg_floor (x : ℝ) :
    ⌊x⌋ + ⌊-x⌋ = if x ∈ Set.range Int.cast then 0 else -1 := by
  -- We have `⌊-x⌋ = -⌈x⌉`.
  rw [Int.floor_neg]
  split_ifs with int
  · -- When `x` is an integer, `⌊x⌋ - ⌈x⌉ = 0` since `⌊x⌋ = ⌈x⌉ = x`.
    obtain ⟨x, ⟨_⟩⟩ := int
    simp
  · -- When `x` is not an integer, we have `⌈x⌉ = ⌊x⌋ + 1`.
    suffices ⌈x⌉ = ⌊x⌋ + 1 by omega
    apply le_antisymm
    · -- We have `⌈x⌉ ≤ ⌊x⌋ + 1` since `x < ↑⌊x⌋ + 1`.
      rw [Int.ceil_le]
      simpa using le_of_lt (Int.lt_floor_add_one _)
    · -- Assuming the converse direction is not true, we would have `x ≤ ↑⌊x⌋`,
      -- and with `↑⌊x⌋ ≤ x`, we get `x = ↑⌊x⌋`, meaning `x` is an integer, a contradiction.
      by_contra h
      rw [Int.add_one_le_ceil_iff, not_lt] at h
      rw [le_antisymm h (Int.floor_le x)] at int
      simp at int

/-- For any $x$, we have $\lim\limits_{n \to +\infty} \frac{\lfloor nx \rfloor}{n} = x$. -/
lemma tendsto_floor_div (x : ℝ) :
    Tendsto (fun n : ℤ => (⌊n * x⌋ : ℝ) / n) atTop (𝓝 x) := by
  -- Rewrite it equivalently as $x - \frac{\{nx\}}{n}$.
  apply Tendsto.congr' (f₁ := fun n : ℤ => x - Int.fract (n * x) / n)
  · -- For sufficiently large `n` (in fact, `n ≥ 1`), the two functions are equal.
    -- We need the denominator to be non-zero.
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    field_simp
    ring_nf
    apply Int.self_sub_fract
  · -- Rewrite `x` as `x - 0` and use the subtraction rule for limits `Tendsto.sub`.
    conv => enter [3]; rw [← sub_zero x]
    refine .sub (by simp) ?_
    -- Now we only need to show $\lim\limits_{n \to +\infty} \frac{\{nx\}}{n} = 0$.
    -- Since $0 \leq \frac{\{nx\}}{n} \leq n^{-1}$ holds for sufficiently large `n`,
    -- and $\lim\limits_{n \to +\infty} n^{-1} = 0$, the proof is complete.
    apply squeeze_zero' (g := fun n : ℤ => (n : ℝ)⁻¹)
    · -- For `n ≥ 0`, we have $0 \leq \frac{\{nx\}}{n}$.
      rw [Filter.eventually_atTop]
      exact ⟨0, fun n hn => div_nonneg (Int.fract_nonneg _) (by simpa)⟩
    · -- For `n ≥ 1`, we have $\frac{\{nx\}}{n} \le n^{-1}$.
      simp only [eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      rw [← one_div, div_le_div_iff_of_pos_right (by simp; omega)]
      exact le_of_lt (Int.fract_lt_one _)
    · -- The limit $\lim\limits_{n \to +\infty} n^{-1} = 0$.
      exact Tendsto.comp tendsto_inv_atTop_zero tendsto_intCast_atTop_atTop

/-- II. (50 points) Find all real triples $(a, b, c)$ such that for any integer $n$,
  we have $[n a] + [n b] = [n c]$. Here, $[x]$ denotes the greatest integer not exceeding
  the real number $x$. -/
theorem number_theory_327957 (a b c : ℝ) :
    (∀ n : ℤ, ⌊n * a⌋ + ⌊n * b⌋ = ⌊n * c⌋) ↔
    (∃ (m n : ℤ) (t : ℝ),
      (a, b, c) = (↑m,  t,      ↑m +  t) ∨
      (a, b, c) = ( t, ↑n,      ↑n +  t) ∨
      (a, b, c) = (↑m, ↑n, (m : ℝ) + ↑n)) := by
  simp only [Prod.mk.injEq]
  -- The condition in the problem is equivalent to:
  -- "At least one of `a` or `b` is an integer, and `c = a + b`."
  transitivity (a ∈ Set.range Int.cast ∨ b ∈ Set.range Int.cast) ∧ c = a + b
  · refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
    · -- Prove that the condition `∀ n : ℤ, ⌊n * a⌋ + ⌊n * b⌋ = ⌊n * c⌋` implies that
      -- at least one of `a` or `b` is an integer. Substituting `n = -1` and `n = 1` and adding,
      -- we get `(⌊a⌋ + ⌊-a⌋) + (⌊b⌋ + ⌊-b⌋) = ⌊c⌋ + ⌊-c⌋`. If neither `a` nor `b` is an integer,
      -- then by the lemma `add_floor_neg_floor`, the left-hand side equals `-2`, while
      -- the right-hand side could be `0` or `-1`, making the equality impossible.
      replace h : (?_ : ℤ) + ?_ = ?_ + ?_ := by congr 1; exact h 1; exact h (-1)
      simp at h
      convert_to (⌊a⌋ + ⌊-a⌋) + (⌊b⌋ + ⌊-b⌋) = ⌊c⌋ + ⌊-c⌋ at h
      · ring
      · by_contra hab
        simp only [not_or] at hab
        simp only [add_floor_neg_floor, hab, ↓reduceIte] at h
        split_ifs at h <;> simp at h
    · -- Prove `c = a + b`. In Lean, `(a + b) / c` can be split into `a / c + b / c`
      -- unconditionally (no need for `c ≠ 0`), and similarly for subtraction.
      -- Then, using the lemma `tendsto_floor_div` to take the limit of the function
      -- `f(n) = ⌊n a⌋ + ⌊n b⌋ - ⌊n c⌋`, we obtain `a + b - c = 0`.
      suffices a + b - c = 0 by linarith
      apply tendsto_nhds_unique
        (f := fun n : ℤ => (⌊n * a⌋ + ⌊n * b⌋ - ⌊n * c⌋ : ℝ) / n) (l := atTop)
      · simpa only [add_div, sub_div] using
          .sub (.add (tendsto_floor_div a) (tendsto_floor_div b)) (tendsto_floor_div c)
      · norm_cast
        simp [h]
    · -- Given that at least one of `a` or `b` is an integer and `c = a + b`,
      -- prove the functional equation holds.
      intro n
      rcases h with ⟨h, ⟨_⟩⟩
      rw [mul_add]
      -- Without loss of generality, assume `a` is an integer; otherwise, swap `a` and `b`.
      wlog ha : a ∈ Set.range Int.cast
      · convert this b a n h.symm (h.resolve_left ha) using 1 <;>
          simp [add_comm]
      · obtain ⟨a, ⟨_⟩⟩ := ha
        norm_cast
        rw [Int.floor_int_add, Int.floor_intCast]
  · -- Prove that our condition is equivalent to the answer given in the problem:
    -- `(a, b, c)` equals `(m, t, m + t)`, `(t, n, n + t)`, or `(m, n, m + n)`.
    constructor
    · rintro ⟨⟨a, ⟨_⟩⟩ | ⟨b, ⟨_⟩⟩, ⟨_⟩⟩
      · exact ⟨a, 0, b, by simp⟩
      · exact ⟨0, b, a, by simp [add_comm]⟩
    · rintro ⟨m, n, t, ⟨⟨_⟩, ⟨_⟩, ⟨_⟩⟩ | ⟨⟨_⟩, ⟨_⟩, ⟨_⟩⟩ | ⟨⟨_⟩, ⟨_⟩, ⟨_⟩⟩⟩ <;>
        simp [add_comm]
