import Mathlib

/-Points $A$, $B$, and $C$ lie in that order along a straight path where the distance
from $A$ to $C$ is $1800$ meters. Ina runs twice as fast as Eve, and Paul runs twice
as fast as Ina. The three runners start running at the same time with Ina starting at $A$
and running toward $C$, Paul starting at $B$ and running toward $C$, and Eve starting at $C$
and running toward $A$. When Paul meets Eve, he turns around and runs toward $A$. Paul and Ina
both arrive at $B$ at the same time. Find the number of meters from $A$ to $B$.-/
theorem algebra_68013 (vi ve vf b_pos meeting_pos : ℝ) ( hmp: meeting_pos > b_pos)
(hv1: vi = 2*ve) (hv2: vp = 2*vi) (vipos: vi>0) (vepos: ve>0) (vfpos: vf>0)
(htime1: (meeting_pos-b_pos)/vp = (1800 - meeting_pos)/ve)
(htime2: 2*(meeting_pos-b_pos)/vp = b_pos/vi):
b_pos = 800 := by
  -- we first compute all speeds from ve
  rw [hv1] at hv2; ring_nf at hv2
  -- replate all times with the obtained values
  rw [hv2] at htime1 htime2
  rw [hv1] at htime2
  -- we can remove ve variable from equations by multiplying by ve
  apply congr_arg (fun x=> 4*x*ve) at htime1
  apply congr_arg (fun x=> 4*x*ve) at htime2
  ring_nf at htime1 htime2
  rw [mul_assoc meeting_pos, mul_inv_cancel₀ (by linarith),
      mul_assoc b_pos, mul_inv_cancel₀ (by linarith)] at htime1 htime2
  norm_num at htime1 htime2
  -- now we have a simple system that we solve
  linarith