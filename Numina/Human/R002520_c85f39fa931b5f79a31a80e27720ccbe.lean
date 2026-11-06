import Mathlib

/- A power boat and a raft both left dock A on a river and headed downstream. The raft drifted at the speed of the river current. The power boat maintained a constant speed with respect to the river. The power boat reached dock B downriver, then immediately turned and traveled back upriver. It eventually met the raft on the river 9 hours after leaving dock A. How many hours did it take the power boat to go from A to B
(A) 3
(B) 3.5
(C) 4
(D) 4.5
(E) 5
-/

theorem algebra_94521 (d rv pv m: ℝ) (h₀ : 0 < v) (h₁ : 0 < rv ) (h₂ : 0 < pv) (h₃: 0 < m) (h₄ : x ≤ d) (h₅ : rv < pv)
(h : x / rv = 9) (h': d / (pv + rv) + (d - x) / (pv - rv) = 9) : d / (pv + rv) = 4.5 := by
  -- rv is river speed, pv is boat's speed w.r.t. river, d is dock a to dock b distance, m is distance from dock a to meeting point. first define t the time for power boat to get to dock b from dock a
  set t := d / (pv + rv) with ht
  -- now express x using rv and express d using t, then replace d and x from h'
  have hx₁ : x = rv * 9 := by
    field_simp at h
    linarith
  have hd : d = t * (pv + rv) := by
    field_simp at ht
    linarith
  rw [hx₁, hd] at h'
  -- h' is t + (t * (pv + rv) - rv * 9) / (pv - rv) = 9, establish pv-rv > 0 for dividing and then manipulate to get 2 * t * pv = 9 * pv
  have h₅ : 0 < pv - rv  := sub_pos.mpr h₅
  have ht' : 2 * t * pv = 9 * pv := by
    calc
      2 * t * pv = (t * (pv - rv) + t * (pv + rv) - rv * 9 + rv * 9) := by ring
      _ = (t * (pv - rv) + t * (pv + rv) - rv * 9 + rv * 9) / (pv - rv) * (pv - rv) := by field_simp
      _ = (t  + (t * (pv + rv) - rv * 9) / (pv - rv) + rv * 9 / (pv - rv)) * (pv - rv) := by
        field_simp
        ring
      _ = (9 + rv * 9 / (pv - rv)) * (pv - rv) := by rw [h']
      _ = 9 * (pv - rv) + rv * 9 := by
        field_simp
      _ = 9 * pv := by ring
  -- finally cancel and get t = 9/2
  have h₂ : pv ≠ 0 := (ne_of_lt h₂).symm
  field_simp [h₂] at ht'
  linarith