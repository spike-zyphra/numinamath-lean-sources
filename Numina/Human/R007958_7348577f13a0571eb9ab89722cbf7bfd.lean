import Mathlib

/- Soit $\mathrm{f}: \mathbb{Z} \mapsto \mathbb{R}$ une fonction telle que

$$
\mathbf{f}(\mathrm{n}+2)=(f(n+1)+\mathbf{f}(\mathrm{n})) / 2
$$

pour tout entier $n$. On suppose que f est bornée, c'est-à-dire qu'il existe un réel $\mathbf{F}$ tel que $-F \leqslant f(n) \leqslant F$ pour tout $n$.
Démontrer que $f$ est une fonction constante. -/
theorem algebra_605722 (f : ℤ → ℝ) (hf : ∀ n : ℤ, f (n + 2) = (f (n + 1) + f n) / 2) (hbound : ∃ F : ℝ, ∀ n : ℤ, -F ≤ f n ∧ f n ≤ F) :
  ∃ C, ∀ n : ℤ, f n = C := by
  -- Let F be a bound for f.
  rcases hbound with ⟨F, hF⟩
  -- To prove that f is constant, it suffices to show that f(n + 1) = f(n) for all n.
  suffices h : ∀ n : ℤ, f (n + 1) = f n by
    -- Indeed, if f satisfies f(n + 1) = f(n) for all n, f(n) = f(0) for all n.
    refine ⟨f 0, fun n => ?_⟩
    -- It can be proved by induction on n.
    induction n using Int.induction_on with
    | hz => simp
    | hp n ih => rwa [h n]
    | hn n ih =>
      specialize h (-n - 1)
      simp at h
      rwa [← h]
  -- By contradiction, assume for some n, f(n + 1) ≠ f(n).
  by_contra! h
  rcases h with ⟨n, hn⟩
  -- Let Δ_k = f(k + 1) - f(k).
  let Δ k := f (k + 1) - f k
  -- Then 0 < |Δ n| because f(n + 1) ≠ f(n).
  replace hn : 0 < |Δ n| := by
    rw [abs_pos]
    intro h
    simp [Δ] at h
    simp [sub_eq_zero] at h
    exact hn h
  -- The given relation can be rewritten as Δ_{k-1} = -2 Δ_k.
  have hΔ (k : ℤ) : Δ (k - 1) = -2 * Δ k := by
    simp [Δ]
    specialize hf (k - 1)
    ring_nf at hf ⊢
    linear_combination 2 * hf
  -- By induction, Δ_{n-k} = (-2)^k * Δ_n for all k ≥ 0.
  have hΔ2 (k : ℕ) : Δ (n - k) = (-2) ^ k * Δ n := by
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [show n - ↑(k + 1) = n - k - 1 by zify; ring,
          hΔ, ih]
      ring
  -- We can find some k such that 2^k * |Δ n| > 2 * F.
  have ⟨k, hk⟩ : ∃ k : ℕ, 2 ^ k * |Δ n| > 2 * F := by
    -- Indeed, by the Archimedean property, there exists some k such that k * |Δ n| ≥ 2 * F.
    obtain ⟨k, hk⟩ := Archimedean.arch (2 * F) hn
    simp at hk
    use k
    calc 2 ^ k * |Δ n|
      -- 2 ^ k > k
      _ > k * |Δ n| := by
        refine mul_lt_mul_of_pos_right ?_ hn
        norm_cast
        exact Nat.lt_two_pow_self
      _ ≥ 2 * F := hk
  -- Rewrite as |Δ (n - k)| > 2 * F.
  replace hk : |Δ (n - k)| > 2 * F := by
    calc |Δ (n - k)|
      _ = |(-2) ^ k| * |Δ n| := by rw [hΔ2, abs_mul]
      _ = 2 ^ k * |Δ n| := by rw [abs_pow]; simp
      _ > 2 * F := hk
  -- But we can bound |Δ n| by 2 * F.
  have hF' (n : ℤ) : |Δ n| ≤ 2 * F := by
    simp only [Δ]
    rw [abs_le]
    constructor
    all_goals
      linarith only [hF n, hF (n + 1)]
  -- This is a contradiction.
  absurd hk
  simp
  exact hF' _
