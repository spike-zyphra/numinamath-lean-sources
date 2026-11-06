import Mathlib

/- Example 5 In the sequence $\left\{x_{n}\right\}$, $x_{1}=3, x_{2}=2, x_{n}=\frac{x_{n-2} x_{n-1}}{2 x_{n-2}-x_{n-1}}(n \geqslant 3, n \in \mathbf{N})$, find the general term formula of the sequence $\left\{x_{n}\right\}$. -/
theorem algebra_163145 {x : PNat → ℝ} (hx1 : x 1 = 3) (hx2 : x 2 = 2)
    (hxn : ∀ n ≥ 3, x n = (x (n - 2) * x (n - 1)) / (2 * x (n - 2) - x (n - 1))) :
    ∀ n, x n = 6 / (n + 1) := by
  -- define y(n) = x(n) if n > 0 and y(0) = 6
  set y : ℕ → ℝ := fun n => if h : n > 0 then x ⟨n, h⟩ else 6
  -- obviously, x(n) = y(n) for all n > 0
  have h {n : PNat} : x n = y n := by
    simp [y]
    rfl
  -- it is enough to show that y(n) = 6 / (n + 1) for all n ≥ 0
  suffices ∀ n, y n = 6 / (n + 1) by
    intro n
    simp [this, h]
  -- proof by induction
  let rec f : (n : ℕ) → (y n = 6 / (n + 1))
  | 0 => by simp [y]
  | 1 => by simp [y, hx1]; norm_num
  | 2 => by simp [y, hx2]; norm_num
  -- consider y(n + 3)
  | n + 3 => by
    -- we have y(n + 1) = 6 / (n + 2)
    have h1 := f (n + 1)
    -- we have y(n + 2) = 6 / (n + 3)
    have h2 := f (n + 2)
    have hn3 : n + 3 > 0 := by omega
    set m : PNat := ⟨n + 3, hn3⟩ with m_eq
    have hm : 3 ≤ m := by
      rw [←PNat.coe_le_coe]
      simp [m]
    have h3 := hxn _ hm
    simp [h, m] at h3
    rw [h3, ←m_eq]
    -- use the hypothesis x(n) = x(n - 2) * x(n - 1) / (2 * x(n - 2) - x(n - 1))
    -- and get the following equality which needs to be proven
    -- y (n + 1) * y (n + 2) / (2 * y (n + 1) - y (n + 2)) = 6 / ((n + 3) + 1)
    rw [show ↑(m - 2) = n + 1 from rfl, show ↑(m - 1) = n + 2 from rfl]
    -- the equality follows from y(n + 1) = 6 / (n + 2) and y(n + 2) = 6 / (n + 3)
    rw [h1, h2]
    simp
    field_simp
    rw [show (2 : ℝ) * 6 * (↑n + 2 + 1) - (↑n + 1 + 1) * 6 = 6 * (n + 3 + 1) by ring]
    field_simp [show (n : ℝ) + 3 + 1 ≠ 0 by linarith]
    ring
  exact f