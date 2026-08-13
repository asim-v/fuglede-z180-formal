import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessPartitionCoreV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S000
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S001
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S002
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S003
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S004
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S005
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S006
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S007
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S008
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S009
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S010
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D4S011

/-! Generated hash partitions for divisor 4, side U. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveCompletenessV97D4UPredicate (bucket : Nat) (set : RawSet) : Bool :=
  normalizedProjectiveRawSetKeyV89 set % 26 == bucket

def z180K30ProjectiveCompletenessV97D4USourceGrouped : List RawSet :=
  [z180K30ProfileV97D4U00M0000, z180K30ProfileV97D4U00M0001, z180K30ProfileV97D4U00M0002, z180K30ProfileV97D4U00M0003, z180K30ProfileV97D4U00M0004, z180K30ProfileV97D4U00M0005, z180K30ProfileV97D4U00M0006, z180K30ProfileV97D4U00M0007, z180K30ProfileV97D4U00M0008, z180K30ProfileV97D4U00M0009, z180K30ProfileV97D4U00M0010, z180K30ProfileV97D4U00M0011, z180K30ProfileV97D4U00M0012, z180K30ProfileV97D4U00M0013, z180K30ProfileV97D4U00M0014, z180K30ProfileV97D4U00M0015, z180K30ProfileV97D4U00M0016, z180K30ProfileV97D4U00M0017, z180K30ProfileV97D4U00M0018, z180K30ProfileV97D4U00M0019, z180K30ProfileV97D4U00M0020, z180K30ProfileV97D4U00M0021, z180K30ProfileV97D4U00M0022, z180K30ProfileV97D4U00M0023, z180K30ProfileV97D4U00M0024, z180K30ProfileV97D4U00M0025, z180K30ProfileV97D4U00M0026, z180K30ProfileV97D4U00M0027, z180K30ProfileV97D4U00M0028, z180K30ProfileV97D4U00M0029, z180K30ProfileV97D4U00M0030, z180K30ProfileV97D4U00M0031, z180K30ProfileV97D4U00M0032, z180K30ProfileV97D4U00M0033, z180K30ProfileV97D4U00M0034, z180K30ProfileV97D4U00M0035, z180K30ProfileV97D4U00M0036, z180K30ProfileV97D4U00M0037, z180K30ProfileV97D4U00M0038, z180K30ProfileV97D4U00M0039, z180K30ProfileV97D4U00M0040, z180K30ProfileV97D4U00M0041, z180K30ProfileV97D4U00M0042, z180K30ProfileV97D4U00M0043, z180K30ProfileV97D4U00M0044, z180K30ProfileV97D4U00M0045, z180K30ProfileV97D4U00M0046, z180K30ProfileV97D4U00M0047, z180K30ProfileV97D4U00M0048, z180K30ProfileV97D4U00M0049, z180K30ProfileV97D4U00M0050, z180K30ProfileV97D4U00M0051, z180K30ProfileV97D4U00M0052, z180K30ProfileV97D4U00M0053, z180K30ProfileV97D4U00M0054, z180K30ProfileV97D4U00M0055, z180K30ProfileV97D4U00M0056, z180K30ProfileV97D4U00M0057, z180K30ProfileV97D4U00M0058, z180K30ProfileV97D4U00M0059, z180K30ProfileV97D4U00M0060, z180K30ProfileV97D4U00M0061, z180K30ProfileV97D4U00M0062, z180K30ProfileV97D4U00M0063, z180K30ProfileV97D4U00M0064, z180K30ProfileV97D4U00M0065, z180K30ProfileV97D4U00M0066, z180K30ProfileV97D4U00M0067, z180K30ProfileV97D4U00M0068, z180K30ProfileV97D4U00M0069, z180K30ProfileV97D4U00M0070, z180K30ProfileV97D4U00M0071, z180K30ProfileV97D4U01M0000, z180K30ProfileV97D4U01M0001, z180K30ProfileV97D4U01M0002, z180K30ProfileV97D4U01M0003, z180K30ProfileV97D4U01M0004, z180K30ProfileV97D4U01M0005, z180K30ProfileV97D4U01M0006, z180K30ProfileV97D4U01M0007, z180K30ProfileV97D4U01M0008, z180K30ProfileV97D4U01M0009, z180K30ProfileV97D4U01M0010, z180K30ProfileV97D4U01M0011, z180K30ProfileV97D4U01M0012, z180K30ProfileV97D4U01M0013, z180K30ProfileV97D4U01M0014, z180K30ProfileV97D4U01M0015, z180K30ProfileV97D4U01M0016, z180K30ProfileV97D4U01M0017, z180K30ProfileV97D4U01M0018, z180K30ProfileV97D4U01M0019, z180K30ProfileV97D4U01M0020, z180K30ProfileV97D4U01M0021, z180K30ProfileV97D4U01M0022, z180K30ProfileV97D4U01M0023, z180K30ProfileV97D4U01M0024, z180K30ProfileV97D4U01M0025, z180K30ProfileV97D4U01M0026, z180K30ProfileV97D4U01M0027, z180K30ProfileV97D4U01M0028, z180K30ProfileV97D4U01M0029, z180K30ProfileV97D4U01M0030, z180K30ProfileV97D4U01M0031, z180K30ProfileV97D4U01M0032, z180K30ProfileV97D4U01M0033, z180K30ProfileV97D4U01M0034, z180K30ProfileV97D4U01M0035, z180K30ProfileV97D4U01M0036, z180K30ProfileV97D4U01M0037, z180K30ProfileV97D4U01M0038, z180K30ProfileV97D4U01M0039, z180K30ProfileV97D4U01M0040, z180K30ProfileV97D4U01M0041, z180K30ProfileV97D4U01M0042, z180K30ProfileV97D4U01M0043, z180K30ProfileV97D4U01M0044, z180K30ProfileV97D4U01M0045, z180K30ProfileV97D4U01M0046, z180K30ProfileV97D4U01M0047, z180K30ProfileV97D4U01M0048, z180K30ProfileV97D4U01M0049, z180K30ProfileV97D4U01M0050, z180K30ProfileV97D4U01M0051, z180K30ProfileV97D4U01M0052, z180K30ProfileV97D4U01M0053, z180K30ProfileV97D4U02M0000, z180K30ProfileV97D4U02M0001, z180K30ProfileV97D4U02M0002, z180K30ProfileV97D4U02M0003, z180K30ProfileV97D4U02M0004, z180K30ProfileV97D4U02M0005, z180K30ProfileV97D4U02M0006, z180K30ProfileV97D4U02M0007, z180K30ProfileV97D4U02M0008, z180K30ProfileV97D4U02M0009, z180K30ProfileV97D4U02M0010, z180K30ProfileV97D4U02M0011, z180K30ProfileV97D4U02M0012, z180K30ProfileV97D4U02M0013, z180K30ProfileV97D4U02M0014, z180K30ProfileV97D4U02M0015, z180K30ProfileV97D4U02M0016, z180K30ProfileV97D4U02M0017, z180K30ProfileV97D4U02M0018, z180K30ProfileV97D4U02M0019, z180K30ProfileV97D4U02M0020, z180K30ProfileV97D4U02M0021, z180K30ProfileV97D4U02M0022, z180K30ProfileV97D4U02M0023, z180K30ProfileV97D4U03M0000, z180K30ProfileV97D4U03M0001, z180K30ProfileV97D4U03M0002, z180K30ProfileV97D4U03M0003, z180K30ProfileV97D4U03M0004, z180K30ProfileV97D4U03M0005, z180K30ProfileV97D4U03M0006, z180K30ProfileV97D4U03M0007, z180K30ProfileV97D4U03M0008, z180K30ProfileV97D4U03M0009, z180K30ProfileV97D4U03M0010, z180K30ProfileV97D4U03M0011, z180K30ProfileV97D4U03M0012, z180K30ProfileV97D4U03M0013, z180K30ProfileV97D4U03M0014, z180K30ProfileV97D4U03M0015, z180K30ProfileV97D4U03M0016, z180K30ProfileV97D4U03M0017]
def z180K30ProjectiveCompletenessV97D4USourceBucketB00 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 0)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB00 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 0)
def z180K30ProjectiveCompletenessV97D4USourceBucketB01 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 1)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB01 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 1)
def z180K30ProjectiveCompletenessV97D4USourceBucketB02 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 2)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB02 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 2)
def z180K30ProjectiveCompletenessV97D4USourceBucketB03 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 3)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB03 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 3)
def z180K30ProjectiveCompletenessV97D4USourceBucketB04 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 4)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB04 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 4)
def z180K30ProjectiveCompletenessV97D4USourceBucketB05 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 5)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB05 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 5)
def z180K30ProjectiveCompletenessV97D4USourceBucketB06 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 6)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB06 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 6)
def z180K30ProjectiveCompletenessV97D4USourceBucketB07 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 7)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB07 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 7)
def z180K30ProjectiveCompletenessV97D4USourceBucketB08 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 8)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB08 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 8)
def z180K30ProjectiveCompletenessV97D4USourceBucketB09 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 9)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB09 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 9)
def z180K30ProjectiveCompletenessV97D4USourceBucketB10 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 10)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB10 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 10)
def z180K30ProjectiveCompletenessV97D4USourceBucketB11 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 11)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB11 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 11)
def z180K30ProjectiveCompletenessV97D4USourceBucketB12 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 12)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB12 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 12)
def z180K30ProjectiveCompletenessV97D4USourceBucketB13 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 13)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB13 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 13)
def z180K30ProjectiveCompletenessV97D4USourceBucketB14 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 14)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB14 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 14)
def z180K30ProjectiveCompletenessV97D4USourceBucketB15 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 15)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB15 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 15)
def z180K30ProjectiveCompletenessV97D4USourceBucketB16 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 16)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB16 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 16)
def z180K30ProjectiveCompletenessV97D4USourceBucketB17 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 17)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB17 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 17)
def z180K30ProjectiveCompletenessV97D4USourceBucketB18 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 18)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB18 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 18)
def z180K30ProjectiveCompletenessV97D4USourceBucketB19 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 19)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB19 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 19)
def z180K30ProjectiveCompletenessV97D4USourceBucketB20 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 20)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB20 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 20)
def z180K30ProjectiveCompletenessV97D4USourceBucketB21 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 21)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB21 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 21)
def z180K30ProjectiveCompletenessV97D4USourceBucketB22 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 22)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB22 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 22)
def z180K30ProjectiveCompletenessV97D4USourceBucketB23 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 23)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB23 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 23)
def z180K30ProjectiveCompletenessV97D4USourceBucketB24 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 24)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB24 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 24)
def z180K30ProjectiveCompletenessV97D4USourceBucketB25 : List RawSet :=
  (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter (z180K30ProjectiveCompletenessV97D4UPredicate 25)

def z180K30ProjectiveCompletenessV97D4UTargetBucketB25 : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 4).filter
    (z180K30ProjectiveCompletenessV97D4UPredicate 25)

end Fuglede.Z180K30ExceptionalRawV2
