import Mathlib

/- Let $\mathbb{R}_{>0}$ be the set of positive real numbers. Determine all functions $f: \mathbb{R}_{>0} \rightarrow \mathbb{R}_{>0}$ such that  $$ x(f(x)+f(y)) \geqslant(f(f(x))+y) f(y) $$  for every $x, y \in \mathbb{R}_{>0}$. (Belgium) -/
theorem algebra_607737 {f : ℝ → ℝ} (h_pos : ∀ x > 0, f x > 0) :
    (∀ x > 0, ∀ y > 0, x * (f x + f y) ≥ (f (f x) + y) * f y) ↔
    (∃ c > 0, ∀ x > 0, f x = c / x) := by
  constructor
  -- Let $f: \mathbb{R}_{>0} \rightarrow \mathbb{R}_{>0}$ be a function that satisfies the inequality of the problem statement.
  · intro h
    -- We will write $f^{k}(x)=f(f(\cdots f(x) \cdots))$ for the composition of $f$ with itself $k$ times, with the convention that $f^{0}(x)=x$.
    -- Substituting $y=x$ gives $$ x \geqslant f^{2}(x) . $$
    have h1 : ∀ x > 0, x ≥ f (f x) := by
      intro x hx_pos
      specialize h x hx_pos x hx_pos
      ring_nf at h
      replace h : x * 2 * f x ≥ (x + f (f x)) * f x := by
        linarith
      simp at h
      rw [mul_le_mul_iff_of_pos_right (by solve_by_elim)] at h
      linarith
    -- Substituting $x=f(y)$ instead leads to $f(y)+f^{2}(y) \geqslant y+f^{3}(y)$, or equivalently $$ f(y)-f^{3}(y) \geqslant y-f^{2}(y) $$
    have h2 : ∀ y > 0, f y - f^[3] y ≥ y - f^[2] y := by
      intro y hy_pos
      specialize h (f y) (by solve_by_elim) y hy_pos
      rw [mul_comm] at h
      simp at h
      rw [mul_le_mul_iff_of_pos_right (by solve_by_elim)] at h
      simp [Nat.iterate]
      linarith
    -- We can generalize this inequality.
    -- If we replace $y$ by $f^{n-1}(y)$ in the above inequality, we get $$ f^{n}(y)-f^{n+2}(y) \geqslant f^{n-1}(y)-f^{n+1}(y) $$
    -- for every $y \in \mathbb{R}_{>0}$ and for every integer $n \geqslant 1$.
    have h_pos' (m : ℕ) : ∀ x > 0, f^[m] x > 0 := by
      induction' m with m ih
      · simp
      · simp_rw [Function.iterate_succ_apply]
        intro x hx_pos
        apply ih
        exact h_pos x hx_pos
    have h3 : ∀ y > 0, ∀ n ≥ 1, f^[n] y - f^[n+2] y ≥ f^[n-1] y - f^[n+1] y := by
      intro y hy_pos n hn_pos
      cases' n with m
      · simp at hn_pos
      specialize h2 (f^[m] y) ?_
      · apply h_pos' _ _ hy_pos
      simp at h2 ⊢
      repeat rw [← Function.iterate_succ_apply]
      rw [← Function.iterate_succ_apply' f m y] at h2
      rw [← Function.iterate_succ_apply' f (m + 1) y] at h2
      rw [← Function.iterate_succ_apply' f (m + 2) y] at h2
      exact h2
    -- In particular, $f^{n}(y)-f^{n+2}(y) \geqslant y-f^{2}(y) \geqslant 0$ for every $n \geqslant 1$.
    have h4 : ∀ y > 0, ∀ n ≥ 1, f^[n] y - f^[n+2] y ≥ y - f^[2] y := by
      intro y hy_pos n hn_pos
      induction' n, hn_pos using Nat.le_induction with n hn_pos ih
      · simpa using h2 y hy_pos
      specialize h3 y hy_pos (n + 1) (by omega)
      apply le_trans _ h3
      exact ih
    -- Hereafter consider even integers $n=2 m$.
    -- Observe that $$ y-f^{2 m}(y)=\sum_{i=0}^{m-1}\left(f^{2 i}(y)-f^{2 i+2}(y)\right) \geqslant m\left(y-f^{2}(y)\right) $$
    have h5 : ∀ y > 0, ∀ m ≥ 1, y - f^[2 * m] y ≥ m * (y - f^[2] y) := by
      intro y hy_pos m hm_pos
      induction' m, hm_pos using Nat.le_induction with m hm_pos ih
      · simp
      have : f^[2 * m] y - f^[2 * (m + 1)] y ≥ y - f^[2] y := by
        specialize h4 y hy_pos (2 * m) (by omega)
        -- simp at h4
        ring_nf at h4 ⊢
        exact h4
      zify
      linarith
    -- Since $f$ takes positive values, $f^{2m}(y) > 0$ for all $y \in \mathbb{R}_{>0}$, which means $y-f^{2m}(y) < y$ is bounded for any fixed $y$.
    have h6 : ∀ y > 0, ∀ m ≥ 1, y - f^[2 * m] y < y := by
      intro y hy_pos m hm_pos
      cases' m with m
      · simp at hm_pos
      rw [show 2 * (m + 1) = 2 * m + 2 by ring]
      simp [-Function.iterate_succ]
      apply h_pos' _ _ hy_pos
    -- However, if $y-f^{2}(y) > 0$, then $m(y-f^{2}(y))$ would grow unbounded as $m$ increases.
    -- Since we've established that $y-f^{2m}(y) \geq m(y-f^{2}(y))$, this would lead to a contradiction for large enough $m$.
    have h7 : ∀ y > 0, ∀ (m : ℕ), m ≥ 1 → m * (y - f^[2] y) < y := by
      intro y hy_pos m hm_pos
      specialize h5 y hy_pos m hm_pos
      specialize h6 y hy_pos m hm_pos
      linarith
    -- Therefore, it must be the case that $y-f^{2}(y) = 0$, which means $f^{2}(y) = y$ for every $y \in \mathbb{R}_{>0}$.
    have h8 : ∀ y > 0, f^[2] y = y := by
      intro y hy_pos
      specialize h7 y hy_pos
      contrapose! h7
      have : (y - f^[2] y) > 0 := by
        specialize h1 y hy_pos
        simp at h7 ⊢
        linarith +splitNe
      obtain ⟨m, hm⟩ := Archimedean.arch y this
      simp at hm
      use m + 1
      constructor
      · simp
      simp at this ⊢
      ring_nf at hm ⊢
      linarith
    -- The original inequality becomes $$ x f(x) \geqslant y f(y) $$
    -- for every $x, y \in \mathbb{R}_{>0}$.
    have h9 : ∀ x > 0, ∀ y > 0, x * f x ≥ y * f y := by
      intro x hx_pos y hy_pos
      specialize h x hx_pos y hy_pos
      simp at h8
      rw [h8 _ hx_pos] at h
      linarith
    -- Hence, $x f(x)$ is constant.
    obtain ⟨c, h10⟩ : ∃ c, ∀ x > 0, x * f x = c := by
      use 1 * f 1
      intro x hx_pos
      have := h9 x hx_pos 1 (by norm_num)
      have := h9 1 (by norm_num) x hx_pos
      linarith
    -- We conclude that $f(x)=c / x$ for some $c>0$.
    use c
    constructor
    · specialize h10 1 (by norm_num)
      simp at h10
      rw [← h10]
      apply h_pos
      norm_num
    · intro x hx_pos
      specialize h10 x hx_pos
      rw [← h10]
      field_simp
  -- We now check that all the functions of the form $f(x)=c / x$ are indeed solutions of the original problem.
  · intro ⟨c, hc_pos, h⟩ x hx_pos y hy_pos
    -- First, note that all these functions satisfy $f(f(x))=c /(c / x)=x$.
    have h1 : ∀ x > 0, f (f x) = x := by
      intro x hx_pos
      rw [h _ (by solve_by_elim), h _ (by solve_by_elim)]
      field_simp
    rw [h1 x hx_pos]
    -- So it's sufficient to check that $x f(x) \geqslant y f(y)$, which is true since $c \geqslant c$.
    suffices x * f x ≥ y * f y by
      linarith
    rw [h _ hx_pos, h _ hy_pos]
    field_simp
