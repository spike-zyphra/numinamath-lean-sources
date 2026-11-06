import Mathlib
/-A watered circular field (shaded) is inscribed in a square plot of land. The square plot has sides of length 500 meters. What is the area of the land that is not watered? Express your answer to the nearest thousand square meters.
[asy]
draw((0,0)--(10,0)--(10,10)--(0,10)--cycle,linewidth(1));
fill(Circle((5,5),5),gray(0.7));
draw(Circle((5,5),5),linewidth(1));
[/asy]-/
theorem algebra_21888 (r : ℚ) (hr : r = 500/2) (h: π = 3.14)( hs : s = 500 ^ 2  - π * r ^ 2)(hts : ts = Int.fract (s / (1000: ℚ)) )(h2 : ∀ ts ≥ (0.5 : ℚ) ,  ⌈s / 1000⌉ = ss)(h3 : ∀ ts < (0.5 : ℚ), ⌊s / 1000⌋ = ss):
     ss * 1000 = 54000 := by
     --The area that is not watered is the area inside the square but outside the circle. The area of the square is $500\cdot500=250000$ square meters. To find the area of the circle, we note that the diameter of the circle is equal to a side of the square, so the radius is $500/2=250$ meters. Thus, the area of the circle is $\pi 250^2\approx196300$ square meters. Thus, the unwatered region has area $250000-196300\approx\boxed{54000}$ square meters.
     rw[hr] at hs
     ring_nf at hs
     rw[hs] at hts
     rw[h] at hts
     ring_nf at hts
     have h4 : 215 / (4:ℚ) = 53.75  := by norm_num
     rw [h4] at hts
     have hf :  Int.fract (53.75 :ℚ) = 0.75 := by
       rw[Int.fract_eq_iff]
       constructor
       norm_num
       constructor
       norm_num
       use 53
       ring_nf
     rw [hf] at hts
     have heq := h2 ts
     have hc : ts ≥ 0.5 := by
       rw [hts]
       norm_num
     have heq2 := heq hc
     rw [hs] at heq2; rw [h] at heq2; ring_nf at heq2
     rw[← heq2]
     ring_nf
