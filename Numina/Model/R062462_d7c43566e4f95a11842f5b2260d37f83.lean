import Mathlib

open Real

theorem algebra_19391 {f g : ℝ → ℝ} (hf : f = fun x => x + 1) (hg : g = fun x => 2 * x)
    (f_inv g_inv : ℝ → ℝ) (hf_inv : f_inv = fun x => x - 1) (hg_inv : g_inv = fun x => x / 2) :
    f (g_inv (f_inv (f_inv (g (f (5)))))) = 6 := by
  -- $f(5) = 6$
  have f5 : f 5 = 6 := by
    rw [hf]
    norm_num
  -- $g(f(5)) = g(6) = 12$
  have g6 : g (f 5) = 12 := by
    rw [f5]
    rw [hg]
    norm_num
  -- $f^{-1}(g(f(5))) = f^{-1}(12) = 11$
  have f_inv_12 : f_inv (g (f 5)) = 11 := by
    rw [g6]
    rw [hf_inv]
    norm_num
  -- $f^{-1}(f^{-1}(g(f(5)))) = f^{-1}(11) = 10$
  have f_inv_11 : f_inv (f_inv (g (f 5))) = 10 := by
    rw [f_inv_12]
    rw [hf_inv]
    norm_num
  -- $g^{-1}(f^{-1}(f^{-1}(g(f(5))))) = g^{-1}(10) = 5$
  have g_inv_10 : g_inv (f_inv (f_inv (g (f 5)))) = 5 := by
    rw [f_inv_11]
    rw [hg_inv]
    norm_num
  -- $f(g^{-1}(...)) = f(5) = 6$
  rw [g_inv_10]
  rw [hf]
  norm_num