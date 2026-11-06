import Mathlib

open Int

/-Let $\mathbb{R}$ be the set of real numbers. We denote by $\mathcal{F}$ the set of all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that  $$ f(x+f(y))=f(x)+f(y) $$  for every $x, y \in \mathbb{R}$. Find all rational numbers $q$ such that for every function $f \in \mathcal{F}$, there exists some $z \in \mathbb{R}$ satisfying $f(z)=q z$. (Indonesia)-/
theorem algebra_24304 {q : ℚ} : let F := {f : ℝ → ℝ | ∀ x y, f (x + f y) = f x + f y}
(∀ f, f ∈ F → ∃ z, f z = q * z) ↔ (∃ n : ℤ, n ≠ 0 ∧ q = ((n:ℚ) + 1) / n) := by
-- Introduce assumptions and split "iff"
  intro F; constructor
-- For the "if" part, we contrapose the goal first
  · contrapose!; intro hq
  -- Prove the case when $q$ equals $1$, we show that the function $⌊x⌋+1$ matches with the goal
    by_cases tmph1 : q = 1
    · simp [tmph1]; let f : ℝ → ℝ := fun x => floor x + 1
      use f; constructor
      · simp [F, f]; intro x y; norm_cast
        rw [floor_add_int]; ring
      intro z; simp [f]; suffices : z < ⌊z⌋ + 1; linarith
      exact lt_floor_add_one z
  -- If $q$ is not $1$, prove the following lemma which comes from the answers in the reference
    have lm : ∀ a : ℝ, a ∈ Set.Ico 0 1 → ∃ m : ℤ,
    ∀ (n : ℤ), ((m : ℝ) - (q : ℝ) * a) / (q - 1) ≠ n := by
      intro a _; by_contra h; push_neg at h
      obtain ⟨u,hu⟩ := h 0; obtain ⟨v,hv⟩ := h 1
      have unev : v - u ≠ 0 := by
        rify; rw [← hu, ← hv, div_sub_div_same]; ring_nf
        apply inv_ne_zero; norm_cast; simp
        rw [add_comm, ← sub_eq_add_neg, sub_eq_zero]; assumption
      suffices : v - u = 1 / ((q:ℝ) - 1)
      · apply_fun (fun t => 1 / t + 1) at this; simp at this
        rw [← one_div, div_add', add_comm, one_mul] at this; norm_cast at this
        rw [Rat.divInt_eq_div, Int.cast_add, show (1:ℤ)=(1:ℚ) by rfl] at this
        have := hq (v-u) unev; symm at this; contradiction
        norm_cast
      rw [← hv, ← hu, div_sub_div_same]; ring
  -- Construct a new function $g$ using "choose" command and prove it is integer-valued
    choose g' hg' using lm
    let g : ℝ → ℝ := fun x => if hx : x ∈ Set.Ico 0 1 then g' x hx else 1
    have hg : ∀ x, ∃ n : ℤ, g x = n := by
      intro x; simp only [g]; by_cases hx : x ∈ Set.Ico 0 1
      · use (g' x hx); split_ifs; rfl
      use 1; split_ifs; norm_num
  -- let $f$ be the function $g({x})+⌊x⌋$ and prove it matches with the final goal
    let f : ℝ → ℝ := fun x => g (fract x) + ⌊x⌋
    use f; constructor
    · simp [f,F]; intro x y
      obtain ⟨nx, hnx⟩ := hg (fract x); obtain ⟨ny, hny⟩ := hg (fract y)
      rw [hnx, hny]; norm_cast; rw [floor_add_int, fract_add_int, hnx]
      norm_cast; ring
    intro z hz; simp [f] at hz; nth_rw 3 [← fract_add_floor z] at hz
    simp only [g] at hz; split at hz
    · rename_i h'; have := hg' (fract z) h' ⌊z⌋
      rw [mul_add] at hz; apply_fun (fun t => t - (⌊z⌋ : ℝ) - (q : ℝ) * fract z) at hz
      ring_nf at hz; rw [hz, add_comm, ← sub_eq_add_neg] at this
      nth_rw 2 [← mul_one (⌊z⌋:ℝ)] at this
      rw [← mul_sub, mul_div_cancel_right₀] at this; contradiction
      intro h; norm_cast at h; rw [sub_eq_zero] at h; contradiction
    rename_i h'; simp at h'
    suffices : fract z < 1; linarith; exact fract_lt_one z
-- For the "only if" part, prove the following key lemma using "Int.induction_on"
-- This key lemma also comes from the answers in the reference
  have key : ∀ f , f ∈ F → ∀ (k : ℤ), f (k * f 0) = (k + 1) * f 0 := by
    intro f hf k; simp [F] at hf
    induction k using Int.induction_on
    · simp
    · rename_i k ihk; push_cast at *
      nth_rw 2 [add_mul]; rw [one_mul, ← ihk, ← hf, ihk]
      ring_nf
    rename_i k ihk; push_cast at *; ring_nf at ihk
    rw [← add_left_inj (f 0), ← hf]; ring_nf; assumption
-- Apply the key lemma and finish the final goal
  rintro ⟨k, ⟨kne0, hk⟩⟩; intro f hf; use (k * f 0)
  rw [hk, key f hf k]; push_cast; field_simp; ring
