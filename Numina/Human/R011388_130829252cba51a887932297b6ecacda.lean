import Mathlib

/- 3. (GDR 1) Knowing that the system  $$ \begin{aligned} x+y+z & =3, \\ x^{3}+y^{3}+z^{3} & =15, \\ x^{4}+y^{4}+z^{4} & =35, \end{aligned} $$  has a real solution $x, y, z$ for which $x^{2}+y^{2}+z^{2}<10$, find the value of $x^{5}+y^{5}+z^{5}$ for that solution. -/
theorem algebra_24908 {x y z : ℝ} (h1 : x + y + z = 3) (h3 : x^3 + y^3 + z^3 = 15) (h4 : x^4 + y^4 + z^4 = 35) (h2u : x^2 + y^2 + z^2 < 10) :
  x^5 + y^5 + z^5 = 83 := by 

  --We are given three equations. We rewrite them and get them x^2+y^2+z^2 can only be 7 or 11.
  have eqxy : x*y+y*z+z*x = ((x+y+z)^2 - (x^2+y^2+z^2))/2 := by ring
  have eqxyz : x*y*z = ( x^3+y^3+z^3 - (x+y+z) * (x^2+y^2+z^2 - (x*y+y*z+z*x)) )/3 := by ring
  have eq4 : x^4 + y^4 + z^4 = (x^3+y^3+z^3) * (x+y+z) - (x^2+y^2+z^2) * (x*y+y*z+z*x) + (x*y*z) * (x+y+z) := by ring
  simp [h4, h3, h1, eqxy, eqxyz] at eq4
  --Since we konw that x^2+y^2+z^2 < 10, it is 7.
  have h2 : (x ^ 2 + y ^ 2 + z ^ 2) = 7 := by nlinarith
  
  --The rest is simple calculation now.
  have eqxyz : x*y*z = -1 := by nlinarith
  have eqxy : x*y+x*z+y*z = 1 := by nlinarith

  calc
    x^5 + y^5 + z ^ 5 = (x^4+y^4+z^4)*(x+y+z) - (x^3+y^3+z^3)*(x*y+x*z+y*z) + (x*y*z) *(x^2+y^2+z^2) := by ring
    _ = 35*3 - 15*1 + (-1) * 7 := by nlinarith
    _ = 83 := by norm_num 
