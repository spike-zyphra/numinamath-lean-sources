import Mathlib

theorem algebra_515331 {f : ℝ → ℝ} (hf : f = fun x => (Real.cos x)^2) :
    IsLeast {T | 0 < T ∧ f = fun x => f (x + T)} (Real.pi) := by
  -- We need to prove that $\pi$ is the smallest positive period of $f(x) = \cos^2 x$.
  constructor
  · -- First, let's show that $\pi$ is indeed a positive period of $f$.
    constructor
    · -- $\pi > 0$
      exact Real.pi_pos
    · -- $f(x) = f(x + \pi)$ for all $x \in \mathbb{R}$
      funext x
      rw [hf]
      -- $\cos^2(x) = \cos^2(x + \pi)$. Since $\cos(x + \pi) = -\cos(x)$, $\cos^2(x + \pi) = (-\cos(x))^2 = \cos^2(x)$
      have h1 : Real.cos (x + Real.pi) = -Real.cos x := Real.cos_add_pi x
      simp [h1]
  · -- Now, let's prove that $\pi$ is the smallest such period.
    intro T hT
    -- Assume $T > 0$ and $f(x) = f(x + T)$ for all $x \in \mathbb{R}$
    rcases hT with ⟨hTpos, hTperiod⟩
    -- If $T < \pi$, proof that we'll derive a contradiction
    by_contra h
    push_neg at h
    -- Consider $x = \pi/2$: $f(\pi/2) = \cos^2(\pi/2) = 0$ and $f(\pi/2 + T) = \cos^2(\pi/2 + T)$
    have h2 := congr_fun hTperiod (Real.pi / 2)
    -- So $\cos^2(\pi/2 + T) = 0$
    simp [hf] at h2
    -- $\sin(T) = 0$
    have h_sin_eq_zero : Real.sin T = 0 := by
      -- $\cos^2(\pi/2 + T) = 0 \implies \cos(\pi/2 + T) = 0$
      have h_cos : Real.cos (Real.pi / 2 + T) = 0 := sq_eq_zero_iff.mp h2.symm
      -- Using the cosine addition formula: $\cos(\pi/2 + T) = \cos(\pi/2)\cos(T) - \sin(\pi/2)\sin(T) = 0 \cdot \cos(T) - 1 \cdot \sin(T) = -\sin(T)$
      have h_cos_add : Real.cos (Real.pi / 2 + T) = Real.cos (Real.pi / 2) * Real.cos T - Real.sin (Real.pi / 2) * Real.sin T := Real.cos_add (Real.pi / 2) T
      rw [h_cos] at h_cos_add
      have h_sin : Real.sin T = 0 := by
        rw [Real.cos_pi_div_two, Real.sin_pi_div_two] at h_cos_add
        linarith only [h_cos_add]
      exact h_sin
    -- $T = k\pi$ for some integer $k$ since $\sin(T) = 0$ and $\cos(T) = \pm 1$,
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h_sin_eq_zero
    have : k = T / Real.pi := by field_simp [hk]
    -- $0 < k$ since $0 < T$.
    have h_k_gt_zero : 0 < (k : ℝ) := by
      rw [this]
      positivity
    -- $k < 1$ since $T < \pi$
    have h_k_lt_one : (k : ℝ) < 1 := by
      rw [this]
      nlinarith
    norm_cast at h_k_gt_zero h_k_lt_one
    -- This contradicts the fact that k is an integer.
    omega
