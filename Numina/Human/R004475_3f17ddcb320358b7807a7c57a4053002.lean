import Mathlib

/- 117. Let three elements $x, y, z$ of the circular sequence $\breve{\Phi}_{m}$ be arranged such that the distance between $x$ and $y$ is equal to the distance between $y$ and $z$ (Fig. 54). Prove that if $x=y=0$, then $z=0$. -/
theorem number_theory_271817 {m : ℕ} (hm : 0 < m) (d : ZMod m → ZMod m → ZMod m)
    (x y z : ZMod m)
    (hd : ∀ x y, d x y = (x - y).val ⊓ (y - x).val)
    (hxy : d x y = d y z) (hxy1 : x = 0) (hxy2 : y = 0) : z = 0 := by

      -- m is not zero
      have ne_zero : NeZero m := NeZero.of_pos hm

      -- replace x and y with 0
      subst hxy1 hxy2

      -- simplify using defition of distance
      -- then we have 0 = min (-z) z
      norm_num [hd, hd] at hxy

      -- consider when (-z) ≤ z
      by_cases left_right : (-z).val ≤ z.val
      -- then z is 0
      · norm_num [left_right] at hxy
        tauto

      -- consider when z ≤ (-z)
      have right_left : z.val ≤ (-z).val := by linarith

      -- then -z is 0 so z is 0
      norm_num [right_left] at hxy
      tauto