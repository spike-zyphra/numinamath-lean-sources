import Mathlib

theorem algebra_717 : IsGreatest {r * v * z - r * w * y - s * u * z + s * w * x + t * u * y - t * v * x | (r : ℤ) (s : ℤ) (t : ℤ) (u : ℤ) (v : ℤ) (w : ℤ) (x : ℤ) (y : ℤ) (z : ℤ) (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (hw : w = 1 ∨ w = -1) (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) (hz : z = 1 ∨ z = -1)} 4 := by
  constructor
  · -- Show that 4 is in the set
    use 1, -1, 1, 1, 1, -1, 1, 1, 1
    norm_num
  · -- Show that 4 is greatest
    intro a ha
    rcases ha with ⟨r, s, t, u, v, w, x, y, z, hr, hs, ht, hu, hv, hw, hx, hy, hz, h⟩
    have hr1 : r = 1 ∨ r = -1 := hr
    have hs1 : s = 1 ∨ s = -1 := hs
    have ht1 : t = 1 ∨ t = -1 := ht
    have hu1 : u = 1 ∨ u = -1 := hu
    have hv1 : v = 1 ∨ v = -1 := hv
    have hw1 : w = 1 ∨ w = -1 := hw
    have hx1 : x = 1 ∨ x = -1 := hx
    have hy1 : y = 1 ∨ y = -1 := hy
    have hz1 : z = 1 ∨ z = -1 := hz
    rcases hr1 with (r1 | r1)
    all_goals
      rcases hs1 with (s1 | s1)
      all_goals
        rcases ht1 with (t1 | t1)
        all_goals
          rcases hu1 with (u1 | u1)
          all_goals
            rcases hv1 with (v1 | v1)
            all_goals
              rcases hw1 with (w1 | w1)
              all_goals
                rcases hx1 with (x1 | x1)
                all_goals
                  rcases hy1 with (y1 | y1)
                  all_goals
                    rcases hz1 with (z1 | z1)
                    all_goals
                      simp only [r1, s1, t1, u1, v1, w1, x1, y1, z1] at h ⊢
                      omega