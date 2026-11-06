import Mathlib
open Polynomial
/- There exist constants $r,$ $s,$ and $t$ so that
\[p(n) = rp(n - 1) + sp(n - 2) + tp(n - 3)\]for any quadratic polynomial $p(x),$ and any integer $n.$  Enter the ordered triple $(r,s,t).$ -/
theorem algebra_21707 {r s t : ℝ} (h :∀ p : Polynomial ℝ, p.natDegree = 2 → ∀ n : ℤ, Polynomial.eval (↑n : ℝ) p= r * Polynomial.eval ↑(n - 1) p + s * Polynomial.eval ↑(n - 2) p + t * Polynomial.eval ↑(n - 3) p) : (r, s, t) = (3, -3, 1):= by
    let p : Polynomial ℝ := X ^ 2
    have hp : p = X ^ 2:= by rfl
    have hde : p.natDegree = 2:= by
        rw [hp]
        compute_degree
        simp
    specialize h p hde
    rw [hp] at h
    simp at h
    -- 使用假设 h，分别代入 n = 0, 1, 2 得到三个等式
    have h1 := h 0 -- 代入 n = 0 得到第一个方程
    have h2 := h 1 -- 代入 n = 1 得到第二个方程
    have h3 := h 2 -- 代入 n = 2 得到第三个方程
    -- 化简这些等式，使用 ring_nf 进行代数化简
    ring_nf at h1 h2 h3
    -- 通过解线性方程组得到 r, s, t 的值
    have h4 : r = 3 := by linarith    -- 使用 linarith 证明 r = 3
    have h5 : s = -3 := by linarith   -- 使用 linarith 证明 s = -3
    have h6 : t = 1 := by linarith    -- 使用 linarith 证明 t = 1
    -- 组合结果，证明 (r, s, t) = (3, -3, 1)
    simp
    exact ⟨h4, h5, h6⟩
