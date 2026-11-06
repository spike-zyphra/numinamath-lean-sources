import Mathlib

/- Antal and Béla set off from Hazul to Cegléd on their motorcycles. From the one-fifth point of the journey, Antal turns back for some reason, which causes him to "switch gears," and he manages to increase his speed by a quarter. He immediately sets off again from Hazul. Béla, traveling alone, reduces his speed by a quarter. They eventually meet again and travel the last part of the journey together at a speed of $48 \mathrm{~km} /$ hour, arriving 10 minutes later than planned. What can we calculate from this? -/
theorem algebra_258450 (d splitPos meetPos: ℝ) (h₀ : d > 0 ∧ meetPos > 0) (hsplit: splitPos = d/5) (v_ab v_a v_b vf : ℝ)
(hpos: v_ab > 0 ∧ vf > 0)
(hva: v_a = v_ab * 5 / 4) (hvb: v_b = v_ab * 3 / 4) (hvf: vf = 48)
(hmeet: splitPos/v_ab + splitPos/v_a + meetPos/v_a = splitPos/v_ab + (meetPos - splitPos)/v_b)
(hArrival: splitPos/v_ab + splitPos/v_a + meetPos/v_a + (d - meetPos)/vf = d/v_ab + 1/6)
  : d=40 := by
  -- first write meetPos in terms of d from hmeet
  rw [hva, hvb] at hmeet
  apply congr_arg (fun x => x * v_ab) at hmeet
  conv_lhs at hmeet =>
    calc _
    _ = splitPos * (v_ab / v_ab) + splitPos * v_ab / (v_ab * 5 / 4) + meetPos * v_ab  / (v_ab * 5 / 4) := by ring_nf
    _ = splitPos * (v_ab / v_ab) + splitPos * (v_ab / v_ab) * 4 / 5 + meetPos * (v_ab  / v_ab) * 4 / 5 := by ring_nf
    _ = splitPos + splitPos * 4 / 5 + meetPos * 4/5 := by rw [ show v_ab / v_ab=1 by (rw [div_self (by linarith)]), mul_one]; ring_nf
    _ = splitPos * 9 / 5 + meetPos * 4/5 := by ring_nf
  conv_rhs at hmeet =>
    calc _
    _ =  (splitPos * (v_ab / v_ab) + (meetPos - splitPos) *(v_ab / v_ab) * 4/3) := by ring_nf
    _ =  (splitPos + (meetPos - splitPos) * 4/3) := by rw [show v_ab / v_ab=1 by (rw [div_self (by linarith)]), mul_one]; ring_nf
    _ =  meetPos * 4/3 - splitPos * 1/3 := by ring_nf
  -- now it's easy to see that meetPos = 4 * splitPos
  have hmeet' : meetPos = 4 * splitPos := by
    linarith
  -- therefore they meet at 4/5 of the way
  rw [hsplit] at hmeet'
  -- now we can simply plug the values into hArrival and solve for d
  rw [hmeet', hva, hsplit, hvf] at hArrival
  ring_nf at hArrival; simp at hArrival; linarith