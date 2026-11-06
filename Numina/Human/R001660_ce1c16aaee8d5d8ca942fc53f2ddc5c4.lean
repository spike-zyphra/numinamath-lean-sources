import Mathlib

/- 9. A3 (BLR) Find all pairs of functions
$f: \mathbb{R} \rightarrow \mathbb{R}, g: \mathbb{R} \rightarrow \mathbb{R}$ such that
$$ f(x+g(y))=x f(y)-y f(x)+g(x) \quad \text { for all } x, y \in R $$-/
theorem algebra_25031 {f g: ℝ → ℝ}:
  (∀(x y:ℝ), f (x+g y) = x*(f y) - y*(f x) + g x) ↔
  (∃ c:ℝ, c ≠ -1 ∧
    (∀x, f x = (c*x - c^2)/(1+c)) ∧
    (∀x, g x = c*x - c^2)   ) := by
  constructor

  · intro h
    -- the proof mainly consists of two parts.
    -- first, we claim exist a such g(a) = 0.
    -- second, using g(a) = 0 solving f and g.

    -- part 1. there exist a, such that g(a) = 0
    have: ∃ a, g a = 0 := by
      by_cases hf0: f 0 = 0
      · -- if f0 = 0, we can use a = - g0
        specialize h (- g 0) 0
        simp only [neg_add_cancel, hf0, mul_zero, zero_mul,
        sub_self, zero_add] at h
        use (- g 0)
        exact h.symm
      · -- otherwise, suppose b = f0 ≠ 0
        set b := f 0 with b_def
        -- replace x by g(x) in the given condition
        have h1 (x y:ℝ): f (g x + g y) = (g x * f y) -
          y * (f (g x)) + (g (g x)) := by
          rw [h (g x) y]
        -- swap x,y in h1
        have h2 (x y:ℝ): f (g x + g y) = (g y * f x) -
          x * (f (g y)) + (g (g y)) := by
          rw [add_comm (g x) (g y), h1 y x]
        -- let a =  g0.
        set a := g 0 with a_def
        -- and f(g(y)) = a - by
        have h3 (y:ℝ) : f (g y) = a - b*y := by
          -- use x=0 at h
          specialize h 0 y
          simp only [zero_add, zero_mul, ← b_def, zero_sub] at h
          rw [h, a_def]; ring
        -- so exist c, f(c) = 0
        obtain ⟨c, hc⟩ : ∃ c, f c = 0 := by
          have: a - b * (a/b) = 0 := by
            field_simp [hf0]
          use (g (a/b))
          rw [h3, this]
        -- use c at h1 h2
        set k := g c with k_def
        set d := a*c + (g k) with d_def
        -- now we have g(g(x)) = kf(x) - ax + d, for some k and d.
        have h4 (x:ℝ): g (g x) = k * f x - a*x + d := by
          have := h1 x c
          rw [h3 x, h2, hc, ← k_def] at this
          simp only [mul_zero, zero_sub] at this
          replace: g (g x) = k * (f x) - (b*c + f k) * x
            + (a*c + g k) := by
            linarith only [this]
          have ha: b*c + f k = a := by
            specialize h3 c
            rw [k_def]
            linarith only [h3]
          rwa [ha, ← d_def] at this
        -- substitute g(gx) to h1 h2
        have h5 (x y: ℝ): (g x) * (f y) + k * (f x) =
          (g y) * (f x) + k * (f y) := by
          specialize h1 x y
          specialize h2 x y
          rw [h4] at h1 h2
          rw [h2, h3 y, h3 x] at h1
          linarith only [h1]
        -- take y=0 at h5
        have h6 (x:ℝ): g x = (a-k)/b * f x + k := by
          specialize h5 x 0
          rw [← b_def, ← a_def] at h5
          field_simp only [hf0]
          linarith only [h5]
        -- if a=k, g is constant, which is impossible
        have anek: a ≠ k := by
          rintro aeqk
          simp only [aeqk, sub_self, zero_div,
          zero_mul, zero_add] at h6
          have: a - b = a - b*2 := by
            have hh1 := h3 1
            have hh2 := h3 2
            simp only [h6, mul_one] at hh1 hh2
            rw [← hh1, hh2]
          simp only [mul_two, sub_right_inj,
          self_eq_add_right] at this
          apply hf0 this
        replace anek: a-k ≠ 0 := by
          rintro hh
          absurd anek
          linarith only [hh]
        -- therefore g(x) = 0 when f(x) = - kb/(a-k)
        -- and we see f(x) is surjective, so exist such x0
        obtain ⟨x0, hx0⟩ : ∃ x0, f x0 = - k*b / (a-k) := by
          obtain ⟨y, hy⟩: ∃ y, a - b*y = - k*b / (a-k) := by
            use ((k/(a-k)) +(a/b))
            field_simp only [anek, hf0]
            ring
          use (g y)
          rw [h3, hy]
        use x0
        rw [h6 x0, hx0]
        field_simp [hf0, anek]
        ring

    -- part 2. now, suppose g(a) = 0
    rcases this with ⟨a, ha⟩
    -- then we claim f is of the form f (x+n) = mx
    obtain ⟨m, n, hf, meqn_imply⟩: ∃ m n, (∀x, f (x+n) = m*x) ∧
      (m=n → (a=0 ∨ f (a+1) - f a = 0)) := by
      -- use y=a at h
      have h1 (x:ℝ): g x = (a+1) * (f x) - x * f a := by
        specialize h x a
        simp only [ha, add_zero] at h
        linarith only [h]
      -- substitute g(x) into h, use y = a+1, done.
      use (f (a+1) - f a), (g (a+1))
      constructor
      · intro x
        specialize h x (a+1)
        rw [h, h1 x]
        ring
      · intro h2
        rw [h1 (a+1)] at h2
        rw [← mul_eq_zero]
        linarith only [h2]
    -- thus we see f is a linear function.
    replace hf: ∀x, f x = m * x - m*n := by
      intro x
      have:f x = f (x-n + n) := by simp
      rw [this, hf, mul_sub]
    -- then f (x+gy) = m(x+g(y)) - mn
    have hg1: ∀(x y:ℝ), m * (x + g y) - m*n = x* f y - y*f x + g x := by
      intro x y
      rw [← hf, h]
    -- re-arrange hg
    have hg2: ∀(x:ℝ), (m-1)*g x = -m*x + m*n := by
      intro x
      specialize hg1 x x
      rw [hf x] at hg1
      simp only [sub_self, zero_add] at hg1
      linarith only [hg1]
    have hg3 (x y:ℝ): m * g y - g x =
      m*n*y - (m*n+m)*x + m*n := by
      specialize h x y
      rw [hf (x+g y), hf y, hf x] at h
      linarith only [h]
    -- m ≠ 1, otherwise contradiction.
    have mne1: m ≠ 1 := by
      rintro rfl
      have h1 := hg2 1
      have h2 := hg2 2
      simp only [sub_self, zero_mul, mul_one,
      one_mul, neg_mul] at h1 h2
      linarith only [h1, h2]
    have mne1': 1-m ≠ 0 := by
      rintro hh
      absurd mne1
      linarith only [hh]
    -- then m-1 ≠ 0, and g(x) = (m/(1-m))x + (m/(1-m))n
    replace hg2 (x:ℝ): g x = (m/(1-m))*x + (m/(1-m))*(-n) := by
      field_simp [mne1']
      specialize hg2 x
      linarith only [hg2]
    -- obviously, gn = 0
    have hgn: g n = 0 := by
      rw [hg2 n]
      ring
    -- if m = 0, trivial.
    by_cases hmz: m = 0
    · use 0
      simp only [hmz, zero_mul, sub_self, sub_zero, div_one,
      mul_neg, neg_zero, add_zero] at hf hg2
      simp [hf, hg2]

    -- compare these coefficients, we can express n in terms of m.
    have hmn: n = m ∨ n = m/(1-m) := by
      -- take x=m, y=n at hg3; take x=m at hg2
      specialize hg3 m n
      rw [hgn] at hg3
      simp only [mul_zero, zero_sub] at hg3
      specialize hg2 m
      rw [hg2] at hg3
      field_simp [mne1'] at hg3
      have: (m-n) * m * (m*n - n + m) = 0 := by
        linarith only [hg3]
      -- m ≠ 0, so n = m or n = m/(1-m)
      rcases (mul_eq_zero.mp this) with hh | hh
      · simp only [mul_eq_zero, hmz, or_false] at hh
        left; linarith only [hh]
      · right
        field_simp only [mne1']
        linarith only [hh]
    -- but m = n is impossible.
    have mnen: m ≠ n := by
      rintro meqn
      rcases (meqn_imply meqn) with az | fz
      · -- if a = 0, the g0 =0, then mn = 0. contradiction.
        rw [az, hg2] at ha
        field_simp [mne1'] at ha
        simp only [← meqn, mul_eq_zero, or_self] at ha
        apply hmz ha
      · -- f is linear function, f(a+1) - f(a) ≠ 0.
        simp only [hf, sub_sub_sub_cancel_right] at fz
        replace fz: m = 0 := by
          linarith only [fz]
        apply hmz fz
    -- therefore n = m/(1-m)
    replace hmn: n = m / (1-m) := by
      simp [mnen.symm, false_or] at hmn
      exact hmn
    -- done.
    use (m/(1-m))
    refine ⟨?_, ?_, ?_⟩
    · field_simp [mne1']
      linarith only
    · intro x
      rw [hf x, hmn]
      field_simp [mne1']
      ring
    · intro x
      rw [hg2, hmn]
      field_simp [mne1']
      ring

  · -- verification
    rintro ⟨c, cne, hf, hg⟩
    intro x y
    simp only [hf, hg]
    have: 1 + c ≠ 0 := by
      rintro hc
      absurd cne
      linarith only [hc]
    field_simp [this]
    ring