import Mathlib.Tactic

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Real.Sign


@[ext]
structure d2_Point where
  x : ℝ
  y : ℝ

namespace d2_Point
/-theorem neg_inner_product {}-/
def Negtive_InnerProduct (P1 : d2_Point) ( P2 : d2_Point) : ℝ :=
  P1.x*P2.x-P1.y*P2.y

def half_one : ℚ := (1 : Rat) / 2

noncomputable def Complex.sqrt (a : ℂ ) : ℂ  :=
 Complex.cpow a ( half_one : ℂ )


#check half_one

noncomputable def Neg_length (P1 : d2_Point) : ℂ   :=
  Complex.cpow (P1.x^2-P1.y^2 : ℂ ) ( half_one : ℂ )
/-GETTING POINTC FOOT_POINT ON LINE THROUGH POINTA AND POINTB -/
def point_subtraction (P1 : d2_Point) (P2 : d2_Point) : d2_Point where
 x := P1.x - P2.x
 y := P1.y - P2.y

/-
have a := (PB.y - PA.y) / (PB.x - PA.x)
have b := (PA.y * PB.x - PA.x * PB.y) / (PB.x - PA.x)
-/
noncomputable def foot_point (PA : d2_Point) (PB : d2_Point) (PC: d2_Point) : d2_Point where
  x := (PC.x - ((PB.y - PA.y) / (PB.x - PA.x)) * ((PA.y * PB.x - PA.x * PB.y) / (PB.x - PA.x)) + ((PB.y - PA.y) / (PB.x - PA.x)) * PC.y) / (1 + ((PB.y - PA.y) / (PB.x - PA.x))^2)

  y := (((PB.y - PA.y) / (PB.x - PA.x)) * PC.x + ((PB.y - PA.y) / (PB.x - PA.x))^2 * PC.y + ((PA.y * PB.x - PA.x * PB.y) / (PB.x - PA.x))) / (1 + ((PB.y - PA.y) / (PB.x - PA.x))^2)

/-GETTING DISTANCE FROM PC TO LINE THROUGH PA AND PB -/
noncomputable def point_to_line_distance (PA : d2_Point) (PB : d2_Point) (PC: d2_Point) : ℂ :=
 Neg_length (point_subtraction PC (foot_point PA PB PC))



theorem Ic_is_real {PA PB PC IC: d2_Point }
                       (h1 : a = Neg_length (point_subtraction PB PC) )
                       (h2 : b = Neg_length (point_subtraction PC PA) )
                       (h3 : c = Neg_length (point_subtraction PA PB) )
                       (h4 : s = (a + b + c) / 2 )
                       (h5 : xIc = PA.x * a/(2 * (s - c)) + PB.x * b/(2 * (s - c)) - PC.x * c/(2 * (s - c)))
                       (h6 : yIc = PA.y * a/(2 * (s - c)) + PB.y * b/(2 * (s - c)) - PC.y * c/(2 * (s - c)))
                       (h7 : IC.x = xIc.re ∧ IC.y = yIc.re )
                       (h8 : lambdac = Real.sign (Complex.abs a + Complex.abs b - Complex.abs c))
                       (h9 : delta = Complex.sqrt (s * (s - a) * (s - b) * (s - c)))
                       (h10 : rc = lambdac * ( delta / (s - c) ) )
                       :
  xIc.im = 0 ∧ yIc.im = 0 ∧
  point_to_line_distance PA PB IC = rc ∧
  point_to_line_distance PB PC IC =rc ∧
  point_to_line_distance PC PA IC =rc

  :=by sorry
