import Fuglede.Z36Card6DifferenceShard1
import Fuglede.Z36Card6DifferenceShard2
import Fuglede.Z36Card6DifferenceShard3
import Fuglede.Z36Card6DifferenceShard4
import Fuglede.Z36Card6DifferenceShard5
import Fuglede.Z36Card6DifferenceShard6
import Fuglede.Z36Card6DifferenceShard7
import Fuglede.Z36Card6DifferenceShard8
import Fuglede.Z36Card6DifferenceShard9
import Fuglede.Z36Card6DifferenceShard10
import Fuglede.Z36Card6DifferenceShard11
import Fuglede.Z36Card6DifferenceShard12
import Fuglede.Z36Card6DifferenceShard13
import Fuglede.Z36Card6DifferenceShard14
import Fuglede.Z36Card6DifferenceShard15
import Fuglede.Z36Card6DifferenceShard16
import Fuglede.Z36Card6DifferenceShard17
import Fuglede.Z36Card6DifferenceShard18
import Fuglede.Z36Card6DifferenceShard19
import Fuglede.Z36Card6DifferenceShard20
import Fuglede.Z36Card6DifferenceShard21
import Fuglede.Z36Card6DifferenceShard22
import Fuglede.Z36Card6DifferenceShard23
import Fuglede.Z36Card6DifferenceShard24
import Fuglede.Z36Card6DifferenceShard25
import Fuglede.Z36Card6DifferenceShard26
import Fuglede.Z36Card6DifferenceShard27
import Fuglede.Z36Card6DifferenceShard28
import Fuglede.Z36Card6DifferenceShard29
import Fuglede.Z36Card6DifferenceShard30
import Fuglede.Z36Card6DifferenceShard31
import Fuglede.Z36Card6DifferenceShard32
import Fuglede.Z36Card6DifferenceShard33
import Fuglede.Z36Card6DifferenceShard34
import Fuglede.Z36Card6DifferenceShard35

/-! Aggregate dispatch for the 35 kernel-reduced classifier shards. -/

namespace Fuglede

theorem z36_card6_difference_shard_dispatch (a : ZMod 36) (ha : a ≠ 0) :
    ∀ S : z36Card6RemainderCandidates a,
      Z36Card6NineDifferencePatterns (insert 0 (insert a S.1)) := by
  fin_cases a
  · exact (ha rfl).elim
  · exact z36_card6_difference_shard_1
  · exact z36_card6_difference_shard_2
  · exact z36_card6_difference_shard_3
  · exact z36_card6_difference_shard_4
  · exact z36_card6_difference_shard_5
  · exact z36_card6_difference_shard_6
  · exact z36_card6_difference_shard_7
  · exact z36_card6_difference_shard_8
  · exact z36_card6_difference_shard_9
  · exact z36_card6_difference_shard_10
  · exact z36_card6_difference_shard_11
  · exact z36_card6_difference_shard_12
  · exact z36_card6_difference_shard_13
  · exact z36_card6_difference_shard_14
  · exact z36_card6_difference_shard_15
  · exact z36_card6_difference_shard_16
  · exact z36_card6_difference_shard_17
  · exact z36_card6_difference_shard_18
  · exact z36_card6_difference_shard_19
  · exact z36_card6_difference_shard_20
  · exact z36_card6_difference_shard_21
  · exact z36_card6_difference_shard_22
  · exact z36_card6_difference_shard_23
  · exact z36_card6_difference_shard_24
  · exact z36_card6_difference_shard_25
  · exact z36_card6_difference_shard_26
  · exact z36_card6_difference_shard_27
  · exact z36_card6_difference_shard_28
  · exact z36_card6_difference_shard_29
  · exact z36_card6_difference_shard_30
  · exact z36_card6_difference_shard_31
  · exact z36_card6_difference_shard_32
  · exact z36_card6_difference_shard_33
  · exact z36_card6_difference_shard_34
  · exact z36_card6_difference_shard_35

#print axioms z36_card6_difference_shard_dispatch

end Fuglede
