import Mathlib

/- 4. Given a function $f:[0,1] \rightarrow[0,1]$ such that $0,1 \in f([0,1])$ and for all $x, y \in[0,1]$ it holds that


$$

|f(x)-f(y)| \leq \frac{|x-f(x)|+|y-f(y)|}{2}

$$


Prove that there exists exactly one number $x \in[0,1]$ such that $f(x)=x$. -/
theorem algebra_248047 (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc 0 1, f x ∈ Set.Icc 0 1)
    (h0 : 0 ∈ f '' Set.Icc 0 1) (h1 : 1 ∈ f '' Set.Icc 0 1)
    (h : ∀ x y , x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → |f x - f y| ≤ (|x - f x| + |y - f y|) / 2) :
    ∃! x, x ∈ Set.Icc 0 1 ∧ f x = x := by
  -- set a, b s.t. f(a) = 0 and f(b) = 0 from hypothesis
  obtain ⟨a, ha, h_fa0⟩ := h0
  obtain ⟨b, hb, h_fb1⟩ := h1
  -- we'll prove a = 1 and b = 0
  have : a = 1 ∧ b = 0 := by
    -- prove 2 ≤ |a| + |b-1| by plugging in a, b in equation
    have hab' := h a b ha hb
    rw [h_fa0, h_fb1] at hab'
    simp at hab'
    have : 2 ≤ |a| + |b-1| := by linarith
    -- prove |a| + |b-1| ≤ 2 by proving each summand is ≤ 1
    have : |a| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith [ha.left, ha.right]
    have : |b-1| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith [hb.left, hb.right]
    have : |a| + |b-1| ≤ 2 := by linarith
    -- this proves |a| = 1, |b-1| = 1, due to range of a, b this proves a = 1, b = 0
    have ha' : |a| = 1:= by linarith
    rw [abs_of_nonneg (show 0 ≤ a by linarith [ha.left])] at ha'
    have : |b-1| = 1 := by linarith
    rw [abs_of_nonpos (show b-1 ≤ 0 by linarith [hb.right])] at this
    have hb' : b = 0 := by linarith
    exact ⟨ha', hb'⟩
  obtain ⟨ha, hb⟩ := this
  subst ha hb
  clear ha hb
  -- next prove f(1/2) ≤ 1/2
  have h_half_ub : f ((1:ℝ)/2) ≤ (1:ℝ)/2 := by
    by_contra h_half_lb
    simp [-one_div] at h_half_lb
    -- if not then plugging in (1/2) and 1 into equation we get contradiction
    have := calc
      2 * f (1/2:ℝ) = 2 * |f (1/2:ℝ) - f 1| := by
        rw [h_fa0]
        simp [-one_div]
        rw [abs_of_pos (by linarith)]
      _ ≤ |(1/2:ℝ) - f (1/2:ℝ)| + |1 - f 1| := by linarith [h (1/2:ℝ) 1 (by norm_num) (by norm_num)]
      _ = f (1/2:ℝ) + (1/2:ℝ) := by
        rw [h_fa0, abs_of_nonpos (by linarith)]
        norm_num; ring
    linarith
  -- prove f(1/2) ≥ 1/2
  have h_half_lb : f ((1:ℝ)/2) ≥ (1:ℝ)/2 := by
    by_contra h_half_ub
    simp [-one_div] at h_half_ub
    -- if not then plugging in (1/2) and 0 into equation we get contradiction
    have := calc
      2 * (1 - f (1/2:ℝ)) = 2 * |f (1/2:ℝ) - f 0| := by
        rw [h_fb1, abs_of_nonpos (by linarith)]
        ring
      _ ≤ |(1/2:ℝ) - f (1/2:ℝ)| + |0 - f 0| := by linarith [h (1/2:ℝ) 0 (by norm_num) (by norm_num)]
      _ = (3/2:ℝ) - f (1/2:ℝ) := by
        rw [h_fb1, abs_of_nonneg (by linarith)]
        norm_num; ring
    linarith
  -- so f(1/2) = 1/2, we'll use this as the unique existence proof
  have h_half : f (1/2:ℝ) = (1/2:ℝ) := by linarith

  use (1/2:ℝ)
  simp [-one_div]
  norm_num
  constructor
  . assumption
    -- to prove 1/2 is unique, if there is another y such that f(y) = 1/2 plug in y and 1/2 into equation to get |y - 1/2| ≤ 0, hence y = 1/2
  . rintro y hy₀ hy₁ hy
    have := calc
      2 * |y - (1/2:ℝ)| = 2 * |f y - f (1/2:ℝ)| := by rw [hy, h_half]
      _ ≤ |y - f y| + |(1/2:ℝ) - f (1/2:ℝ)| := by
        have : y ∈ Set.Icc 0 1 := by constructor <;> linarith
        linarith [h y (1/2:ℝ) (show y ∈ Set.Icc 0 1 by assumption) (show (1/2:ℝ) ∈ Set.Icc 0 1 by norm_num)]
      _ = 0 := by rw [hy, h_half]; norm_num
    have : |y - (1/2:ℝ)| = 0 := by linarith [abs_nonneg (y - (1/2:ℝ))]
    have := abs_eq_zero.mp this
    linarith