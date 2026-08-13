-- Generator SHA-256: 950682432c432f362d3d6da2b2a55eae5e2e46d66690481fba2a0b696adc323b
import Fuglede.Z180K12M6Order36FibreTableZeroZero
import Fuglede.Z180K12M6Order36FibreTableZeroBalancedOne
import Fuglede.Z180K12M6Order36FibreTableZeroBalancedTwo
import Fuglede.Z180K12M6Order36FibreTableZeroBalancedThree
import Fuglede.Z180K12M6Order36FibreTableZeroPositive
import Fuglede.Z180K12M6Order36FibreTableZeroNegative
import Fuglede.Z180K12M6Order36FibreTableBalancedOneZero
import Fuglede.Z180K12M6Order36FibreTableBalancedOneBalancedOne
import Fuglede.Z180K12M6Order36FibreTableBalancedOneBalancedTwo
import Fuglede.Z180K12M6Order36FibreTableBalancedOneBalancedThree
import Fuglede.Z180K12M6Order36FibreTableBalancedOnePositive
import Fuglede.Z180K12M6Order36FibreTableBalancedOneNegative
import Fuglede.Z180K12M6Order36FibreTableBalancedTwoZero
import Fuglede.Z180K12M6Order36FibreTableBalancedTwoBalancedOne
import Fuglede.Z180K12M6Order36FibreTableBalancedTwoBalancedTwo
import Fuglede.Z180K12M6Order36FibreTableBalancedTwoBalancedThree
import Fuglede.Z180K12M6Order36FibreTableBalancedTwoPositive
import Fuglede.Z180K12M6Order36FibreTableBalancedTwoNegative
import Fuglede.Z180K12M6Order36FibreTableBalancedThreeZero
import Fuglede.Z180K12M6Order36FibreTableBalancedThreeBalancedOne
import Fuglede.Z180K12M6Order36FibreTableBalancedThreeBalancedTwo
import Fuglede.Z180K12M6Order36FibreTableBalancedThreeBalancedThree
import Fuglede.Z180K12M6Order36FibreTableBalancedThreePositive
import Fuglede.Z180K12M6Order36FibreTableBalancedThreeNegative
import Fuglede.Z180K12M6Order36FibreTablePositiveZero
import Fuglede.Z180K12M6Order36FibreTablePositiveBalancedOne
import Fuglede.Z180K12M6Order36FibreTablePositiveBalancedTwo
import Fuglede.Z180K12M6Order36FibreTablePositiveBalancedThree
import Fuglede.Z180K12M6Order36FibreTablePositivePositive
import Fuglede.Z180K12M6Order36FibreTablePositiveNegative
import Fuglede.Z180K12M6Order36FibreTableNegativeZero
import Fuglede.Z180K12M6Order36FibreTableNegativeBalancedOne
import Fuglede.Z180K12M6Order36FibreTableNegativeBalancedTwo
import Fuglede.Z180K12M6Order36FibreTableNegativeBalancedThree
import Fuglede.Z180K12M6Order36FibreTableNegativePositive
import Fuglede.Z180K12M6Order36FibreTableNegativeNegative

namespace Fuglede

theorem z180_k12_order36_fibre_table
    (f0 f1 f2 f3 f4 f5 : Z180K12Order36Fibre) :
    Z180K12Order36TableProperty f0 f1 f2 f3 f4 f5 := by
  cases f0 <;> cases f1
  · exact z180_k12_order36_fibre_table_zero_zero f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_zero_balancedOne f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_zero_balancedTwo f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_zero_balancedThree f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_zero_positive f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_zero_negative f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedOne_zero f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedOne_balancedOne f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedOne_balancedTwo f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedOne_balancedThree f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedOne_positive f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedOne_negative f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedTwo_zero f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedTwo_balancedOne f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedTwo_balancedTwo f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedTwo_balancedThree f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedTwo_positive f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedTwo_negative f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedThree_zero f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedThree_balancedOne f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedThree_balancedTwo f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedThree_balancedThree f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedThree_positive f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_balancedThree_negative f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_positive_zero f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_positive_balancedOne f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_positive_balancedTwo f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_positive_balancedThree f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_positive_positive f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_positive_negative f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_negative_zero f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_negative_balancedOne f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_negative_balancedTwo f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_negative_balancedThree f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_negative_positive f2 f3 f4 f5
  · exact z180_k12_order36_fibre_table_negative_negative f2 f3 f4 f5

#print axioms z180_k12_order36_fibre_table

end Fuglede
