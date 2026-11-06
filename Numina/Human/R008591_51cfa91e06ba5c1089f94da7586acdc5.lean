import Mathlib

/- Kim's flight took off from Newark at 10:34 AM and landed in Miami at 1:18 PM. Both cities are in the same time zone. If her flight took h hours and m minutes, with 0< m < 60, what is h+m?
(A) 46(B) 47(C) 50(D) 53(E) 54 -/
theorem algebra_93329 (h m takeoff landing : ℤ) (ht : takeoff = 60 * 10 + 34) (hl : landing = 60 * 12 + 60 * 1 + 18)
(hm : m = (landing - takeoff) % 60) (hh: 60 * h = landing - takeoff - m):
h + m = 46 := by

  --substitute the takoff hour and landing hour to find minutes and hour of the flight
  rw[ht, hl] at hm hh
  rw[hm] at hh
  norm_num at hm hh
  rw[hm]
  have hhh : h = 2 := by 
    rify at hh
    rify
    have hhk := congrFun (congrArg HMul.hMul hh) (1/60)
    ring_nf at hhk
    exact hhk
    
  --compute h + m
  rw[hhh]
  simp