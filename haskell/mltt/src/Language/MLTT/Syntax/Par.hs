{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.MLTT.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pListUnit
  , pUnit
  , pModule
  , pInclude
  , pListInclude
  , pTelescopeDecl
  , pParam
  , pListParam
  , pImport
  , pListImport
  , pDecl
  , pListDecl
  , pDischarge
  , pListVarIdent
  , pTerm
  , pTerm1
  , pTerm2
  , pScopedTerm
  , pPattern
  ) where

import Prelude

import qualified Language.MLTT.Syntax.Abs
import Language.MLTT.Syntax.Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn23 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.VarIdent))
	| HappyAbsSyn24 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Program))
	| HappyAbsSyn25 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Unit]))
	| HappyAbsSyn26 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Unit))
	| HappyAbsSyn27 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Module))
	| HappyAbsSyn28 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Include))
	| HappyAbsSyn29 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Include]))
	| HappyAbsSyn30 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.TelescopeDecl))
	| HappyAbsSyn31 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Param))
	| HappyAbsSyn32 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Param]))
	| HappyAbsSyn33 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Import))
	| HappyAbsSyn34 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Import]))
	| HappyAbsSyn35 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Decl))
	| HappyAbsSyn36 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Decl]))
	| HappyAbsSyn37 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Discharge))
	| HappyAbsSyn38 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.VarIdent]))
	| HappyAbsSyn39 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Term))
	| HappyAbsSyn42 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.ScopedTerm))
	| HappyAbsSyn43 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Pattern))

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62,
 action_63,
 action_64,
 action_65,
 action_66,
 action_67,
 action_68,
 action_69,
 action_70,
 action_71,
 action_72,
 action_73,
 action_74,
 action_75,
 action_76,
 action_77,
 action_78,
 action_79,
 action_80,
 action_81,
 action_82,
 action_83,
 action_84,
 action_85,
 action_86,
 action_87,
 action_88,
 action_89,
 action_90,
 action_91,
 action_92,
 action_93,
 action_94,
 action_95,
 action_96,
 action_97,
 action_98,
 action_99,
 action_100,
 action_101,
 action_102,
 action_103,
 action_104,
 action_105,
 action_106,
 action_107,
 action_108,
 action_109,
 action_110,
 action_111,
 action_112,
 action_113,
 action_114,
 action_115,
 action_116,
 action_117,
 action_118,
 action_119,
 action_120,
 action_121,
 action_122,
 action_123,
 action_124,
 action_125,
 action_126,
 action_127,
 action_128,
 action_129,
 action_130,
 action_131,
 action_132,
 action_133,
 action_134,
 action_135,
 action_136,
 action_137,
 action_138,
 action_139,
 action_140,
 action_141,
 action_142,
 action_143,
 action_144,
 action_145,
 action_146,
 action_147,
 action_148,
 action_149,
 action_150,
 action_151,
 action_152,
 action_153,
 action_154,
 action_155,
 action_156,
 action_157,
 action_158,
 action_159,
 action_160,
 action_161,
 action_162,
 action_163,
 action_164,
 action_165,
 action_166,
 action_167,
 action_168,
 action_169,
 action_170,
 action_171,
 action_172,
 action_173,
 action_174,
 action_175,
 action_176,
 action_177,
 action_178,
 action_179,
 action_180,
 action_181,
 action_182,
 action_183,
 action_184,
 action_185,
 action_186,
 action_187,
 action_188,
 action_189,
 action_190 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27,
 happyReduce_28,
 happyReduce_29,
 happyReduce_30,
 happyReduce_31,
 happyReduce_32,
 happyReduce_33,
 happyReduce_34,
 happyReduce_35,
 happyReduce_36,
 happyReduce_37,
 happyReduce_38,
 happyReduce_39,
 happyReduce_40,
 happyReduce_41,
 happyReduce_42,
 happyReduce_43,
 happyReduce_44,
 happyReduce_45,
 happyReduce_46,
 happyReduce_47,
 happyReduce_48,
 happyReduce_49,
 happyReduce_50,
 happyReduce_51,
 happyReduce_52,
 happyReduce_53,
 happyReduce_54,
 happyReduce_55,
 happyReduce_56,
 happyReduce_57,
 happyReduce_58,
 happyReduce_59,
 happyReduce_60,
 happyReduce_61,
 happyReduce_62,
 happyReduce_63,
 happyReduce_64,
 happyReduce_65,
 happyReduce_66,
 happyReduce_67,
 happyReduce_68,
 happyReduce_69,
 happyReduce_70,
 happyReduce_71,
 happyReduce_72,
 happyReduce_73,
 happyReduce_74,
 happyReduce_75 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,394) ([0,0,0,4096,4,0,0,0,32768,32,0,0,0,0,260,0,0,0,0,32,0,0,0,0,64,0,0,0,0,512,0,0,0,0,0,16,0,0,0,1,0,0,0,0,8,0,0,0,0,0,8,0,0,0,0,64,0,0,0,0,49600,2,0,0,0,3584,22,0,0,0,0,64,0,0,0,0,0,2048,0,0,33024,16641,29665,0,0,2048,12,38922,3,0,16384,96,49232,28,0,0,770,49794,231,0,0,8208,0,1024,0,0,0,0,8192,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4104,0,512,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,192,34976,59,0,0,0,0,0,0,0,0,0,0,0,0,33024,16641,29665,0,0,2048,0,0,0,0,16384,0,0,0,0,0,1026,0,128,0,0,16,0,0,0,0,0,0,0,0,0,1024,0,0,0,0,8192,0,0,0,0,0,513,0,64,0,0,3080,2560,920,0,0,24640,20480,7360,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1540,1280,460,0,0,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,512,0,0,0,0,0,0,0,0,0,1024,1030,53125,1,0,8192,8240,31784,14,0,0,0,0,64,0,0,0,0,512,0,0,0,0,4096,0,0,0,32,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,2048,0,0,0,0,0,0,0,2048,0,0,0,0,0,0,0,0,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,4096,0,0,0,0,0,0,0,0,0,0,0,512,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4096,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,512,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,16384,0,0,0,0,4096,0,0,0,0,0,0,0,0,0,2,0,0,0,0,14336,88,0,0,0,0,0,1024,0,0,0,0,8192,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,32832,0,4096,0,0,512,4,32768,0,0,4096,4120,15892,7,0,0,32,0,0,0,0,1540,34052,463,0,0,12320,10272,3708,0,0,3584,0,0,0,0,2048,2060,40714,3,0,16384,16480,63568,28,0,0,8,0,0,0,0,8208,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,385,57665,115,0,0,3080,2568,927,0,0,256,0,0,0,0,2048,0,0,0,0,4096,4120,15892,7,0,0,1,0,0,0,0,32,0,0,0,0,256,0,0,0,0,33024,16641,29665,0,0,0,0,0,0,0,32768,0,0,0,0,0,0,0,0,0,0,6160,5136,1854,0,0,1024,0,0,0,0,0,0,16,0,0,0,0,2,0,0,0,0,0,0,0,0,3080,2568,927,0,0,2048,0,0,0,0,512,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,8,0,0,0,0,256,0,0,0,0,0,11292,0,0,0,2048,2060,40714,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49280,41088,14832,0,0,1024,1030,53125,1,0,0,0,0,0,0,0,16384,0,0,0,0,3080,2568,927,0,0,24640,20544,7416,0,0,1024,0,0,0,0,8192,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,1,0,0,0,0,770,49794,231,0,0,32,0,0,0,0,256,0,0,0,0,16384,0,0,0,0,0,0,256,0,0,0,385,57665,115,0,0,0,0,0,0,0,0,8,0,0,0,0,22584,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1540,34052,463,0,0,0,0,2,0,0,0,0,1024,0,0,0,0,0,0,0,16384,16480,63568,28,0,0,770,49794,231,0,0,32,0,0,0,0,256,0,0,0,0,1024,1030,53125,1,0,8192,8240,31784,14,0,0,0,0,0,0,0,3080,2568,927,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","%start_pListUnit_internal","%start_pUnit_internal","%start_pModule_internal","%start_pInclude_internal","%start_pListInclude_internal","%start_pTelescopeDecl_internal","%start_pParam_internal","%start_pListParam_internal","%start_pImport_internal","%start_pListImport_internal","%start_pDecl_internal","%start_pListDecl_internal","%start_pDischarge_internal","%start_pListVarIdent_internal","%start_pTerm_internal","%start_pTerm1_internal","%start_pTerm2_internal","%start_pScopedTerm_internal","%start_pPattern_internal","VarIdent","Program","ListUnit","Unit","Module","Include","ListInclude","TelescopeDecl","Param","ListParam","Import","ListImport","Decl","ListDecl","Discharge","ListVarIdent","Term","Term1","Term2","ScopedTerm","Pattern","'('","')'","','","':'","':='","';'","'='","'Id'","'J'","'_'","'check'","'compute'","'def'","'import'","'in'","'include'","'let'","'module'","'namespace'","'open'","'over'","'private'","'refl'","'telescope'","'tt'","'where'","'{'","'}'","'\215'","'\928'","'\931'","'\955'","'\960\8321'","'\960\8322'","'\8594'","'\8658'","'\120140'","'\120793'","L_VarIdent","%eof"]
        bit_start = st Prelude.* 83
        bit_end = (st Prelude.+ 1) Prelude.* 83
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..82]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (61) = happyShift action_75
action_0 (67) = happyShift action_69
action_0 (24) = happyGoto action_81
action_0 (25) = happyGoto action_82
action_0 (26) = happyGoto action_80
action_0 (27) = happyGoto action_77
action_0 (30) = happyGoto action_78
action_0 _ = happyReduce_22

action_1 (61) = happyShift action_75
action_1 (67) = happyShift action_69
action_1 (25) = happyGoto action_79
action_1 (26) = happyGoto action_80
action_1 (27) = happyGoto action_77
action_1 (30) = happyGoto action_78
action_1 _ = happyReduce_22

action_2 (61) = happyShift action_75
action_2 (67) = happyShift action_69
action_2 (26) = happyGoto action_76
action_2 (27) = happyGoto action_77
action_2 (30) = happyGoto action_78
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (61) = happyShift action_75
action_3 (27) = happyGoto action_74
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (59) = happyShift action_72
action_4 (28) = happyGoto action_73
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (59) = happyShift action_72
action_5 (28) = happyGoto action_70
action_5 (29) = happyGoto action_71
action_5 _ = happyReduce_28

action_6 (67) = happyShift action_69
action_6 (30) = happyGoto action_68
action_6 _ = happyFail (happyExpListPerState 6)

action_7 (44) = happyShift action_66
action_7 (31) = happyGoto action_67
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (44) = happyShift action_66
action_8 (31) = happyGoto action_64
action_8 (32) = happyGoto action_65
action_8 _ = happyReduce_32

action_9 (57) = happyShift action_62
action_9 (33) = happyGoto action_63
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (57) = happyShift action_62
action_10 (33) = happyGoto action_60
action_10 (34) = happyGoto action_61
action_10 _ = happyReduce_35

action_11 (54) = happyShift action_53
action_11 (55) = happyShift action_54
action_11 (56) = happyShift action_55
action_11 (62) = happyShift action_56
action_11 (63) = happyShift action_57
action_11 (65) = happyShift action_58
action_11 (35) = happyGoto action_59
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (54) = happyShift action_53
action_12 (55) = happyShift action_54
action_12 (56) = happyShift action_55
action_12 (62) = happyShift action_56
action_12 (63) = happyShift action_57
action_12 (65) = happyShift action_58
action_12 (35) = happyGoto action_51
action_12 (36) = happyGoto action_52
action_12 _ = happyReduce_43

action_13 (64) = happyShift action_50
action_13 (37) = happyGoto action_49
action_13 _ = happyReduce_46

action_14 (82) = happyShift action_21
action_14 (23) = happyGoto action_47
action_14 (38) = happyGoto action_48
action_14 _ = happyReduce_48

action_15 (44) = happyShift action_31
action_15 (51) = happyShift action_32
action_15 (52) = happyShift action_33
action_15 (60) = happyShift action_34
action_15 (66) = happyShift action_35
action_15 (68) = happyShift action_36
action_15 (73) = happyShift action_37
action_15 (74) = happyShift action_38
action_15 (75) = happyShift action_39
action_15 (76) = happyShift action_40
action_15 (77) = happyShift action_41
action_15 (80) = happyShift action_42
action_15 (81) = happyShift action_43
action_15 (82) = happyShift action_21
action_15 (23) = happyGoto action_26
action_15 (39) = happyGoto action_46
action_15 (40) = happyGoto action_28
action_15 (41) = happyGoto action_29
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (44) = happyShift action_31
action_16 (51) = happyShift action_32
action_16 (52) = happyShift action_33
action_16 (66) = happyShift action_35
action_16 (68) = happyShift action_36
action_16 (76) = happyShift action_40
action_16 (77) = happyShift action_41
action_16 (80) = happyShift action_42
action_16 (81) = happyShift action_43
action_16 (82) = happyShift action_21
action_16 (23) = happyGoto action_26
action_16 (40) = happyGoto action_45
action_16 (41) = happyGoto action_29
action_16 _ = happyFail (happyExpListPerState 16)

action_17 (44) = happyShift action_31
action_17 (51) = happyShift action_32
action_17 (52) = happyShift action_33
action_17 (66) = happyShift action_35
action_17 (68) = happyShift action_36
action_17 (76) = happyShift action_40
action_17 (77) = happyShift action_41
action_17 (80) = happyShift action_42
action_17 (81) = happyShift action_43
action_17 (82) = happyShift action_21
action_17 (23) = happyGoto action_26
action_17 (41) = happyGoto action_44
action_17 _ = happyFail (happyExpListPerState 17)

action_18 (44) = happyShift action_31
action_18 (51) = happyShift action_32
action_18 (52) = happyShift action_33
action_18 (60) = happyShift action_34
action_18 (66) = happyShift action_35
action_18 (68) = happyShift action_36
action_18 (73) = happyShift action_37
action_18 (74) = happyShift action_38
action_18 (75) = happyShift action_39
action_18 (76) = happyShift action_40
action_18 (77) = happyShift action_41
action_18 (80) = happyShift action_42
action_18 (81) = happyShift action_43
action_18 (82) = happyShift action_21
action_18 (23) = happyGoto action_26
action_18 (39) = happyGoto action_27
action_18 (40) = happyGoto action_28
action_18 (41) = happyGoto action_29
action_18 (42) = happyGoto action_30
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (44) = happyShift action_24
action_19 (53) = happyShift action_25
action_19 (82) = happyShift action_21
action_19 (23) = happyGoto action_22
action_19 (43) = happyGoto action_23
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (82) = happyShift action_21
action_20 _ = happyFail (happyExpListPerState 20)

action_21 _ = happyReduce_20

action_22 _ = happyReduce_74

action_23 (83) = happyAccept
action_23 _ = happyFail (happyExpListPerState 23)

action_24 (44) = happyShift action_24
action_24 (53) = happyShift action_25
action_24 (82) = happyShift action_21
action_24 (23) = happyGoto action_22
action_24 (43) = happyGoto action_114
action_24 _ = happyFail (happyExpListPerState 24)

action_25 _ = happyReduce_73

action_26 _ = happyReduce_65

action_27 _ = happyReduce_72

action_28 (44) = happyShift action_31
action_28 (51) = happyShift action_32
action_28 (52) = happyShift action_33
action_28 (66) = happyShift action_35
action_28 (68) = happyShift action_36
action_28 (72) = happyShift action_112
action_28 (76) = happyShift action_40
action_28 (77) = happyShift action_41
action_28 (78) = happyShift action_113
action_28 (80) = happyShift action_42
action_28 (81) = happyShift action_43
action_28 (82) = happyShift action_21
action_28 (23) = happyGoto action_26
action_28 (41) = happyGoto action_101
action_28 _ = happyReduce_57

action_29 _ = happyReduce_59

action_30 (83) = happyAccept
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (44) = happyShift action_31
action_31 (51) = happyShift action_32
action_31 (52) = happyShift action_33
action_31 (60) = happyShift action_34
action_31 (66) = happyShift action_35
action_31 (68) = happyShift action_36
action_31 (73) = happyShift action_37
action_31 (74) = happyShift action_38
action_31 (75) = happyShift action_39
action_31 (76) = happyShift action_40
action_31 (77) = happyShift action_41
action_31 (80) = happyShift action_42
action_31 (81) = happyShift action_43
action_31 (82) = happyShift action_21
action_31 (23) = happyGoto action_26
action_31 (39) = happyGoto action_111
action_31 (40) = happyGoto action_28
action_31 (41) = happyGoto action_29
action_31 _ = happyFail (happyExpListPerState 31)

action_32 (44) = happyShift action_110
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (44) = happyShift action_109
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (44) = happyShift action_24
action_34 (53) = happyShift action_25
action_34 (82) = happyShift action_21
action_34 (23) = happyGoto action_22
action_34 (43) = happyGoto action_108
action_34 _ = happyFail (happyExpListPerState 34)

action_35 (44) = happyShift action_107
action_35 _ = happyFail (happyExpListPerState 35)

action_36 _ = happyReduce_64

action_37 (44) = happyShift action_106
action_37 _ = happyFail (happyExpListPerState 37)

action_38 (44) = happyShift action_105
action_38 _ = happyFail (happyExpListPerState 38)

action_39 (44) = happyShift action_24
action_39 (53) = happyShift action_25
action_39 (82) = happyShift action_21
action_39 (23) = happyGoto action_22
action_39 (43) = happyGoto action_104
action_39 _ = happyFail (happyExpListPerState 39)

action_40 (44) = happyShift action_31
action_40 (51) = happyShift action_32
action_40 (52) = happyShift action_33
action_40 (66) = happyShift action_35
action_40 (68) = happyShift action_36
action_40 (76) = happyShift action_40
action_40 (77) = happyShift action_41
action_40 (80) = happyShift action_42
action_40 (81) = happyShift action_43
action_40 (82) = happyShift action_21
action_40 (23) = happyGoto action_26
action_40 (41) = happyGoto action_103
action_40 _ = happyFail (happyExpListPerState 40)

action_41 (44) = happyShift action_31
action_41 (51) = happyShift action_32
action_41 (52) = happyShift action_33
action_41 (66) = happyShift action_35
action_41 (68) = happyShift action_36
action_41 (76) = happyShift action_40
action_41 (77) = happyShift action_41
action_41 (80) = happyShift action_42
action_41 (81) = happyShift action_43
action_41 (82) = happyShift action_21
action_41 (23) = happyGoto action_26
action_41 (41) = happyGoto action_102
action_41 _ = happyFail (happyExpListPerState 41)

action_42 _ = happyReduce_62

action_43 _ = happyReduce_63

action_44 (83) = happyAccept
action_44 _ = happyFail (happyExpListPerState 44)

action_45 (44) = happyShift action_31
action_45 (51) = happyShift action_32
action_45 (52) = happyShift action_33
action_45 (66) = happyShift action_35
action_45 (68) = happyShift action_36
action_45 (76) = happyShift action_40
action_45 (77) = happyShift action_41
action_45 (80) = happyShift action_42
action_45 (81) = happyShift action_43
action_45 (82) = happyShift action_21
action_45 (83) = happyAccept
action_45 (23) = happyGoto action_26
action_45 (41) = happyGoto action_101
action_45 _ = happyFail (happyExpListPerState 45)

action_46 (83) = happyAccept
action_46 _ = happyFail (happyExpListPerState 46)

action_47 (46) = happyShift action_100
action_47 _ = happyReduce_49

action_48 (83) = happyAccept
action_48 _ = happyFail (happyExpListPerState 48)

action_49 (83) = happyAccept
action_49 _ = happyFail (happyExpListPerState 49)

action_50 (44) = happyShift action_99
action_50 _ = happyFail (happyExpListPerState 50)

action_51 (49) = happyShift action_98
action_51 _ = happyReduce_44

action_52 (83) = happyAccept
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (44) = happyShift action_31
action_53 (51) = happyShift action_32
action_53 (52) = happyShift action_33
action_53 (60) = happyShift action_34
action_53 (66) = happyShift action_35
action_53 (68) = happyShift action_36
action_53 (73) = happyShift action_37
action_53 (74) = happyShift action_38
action_53 (75) = happyShift action_39
action_53 (76) = happyShift action_40
action_53 (77) = happyShift action_41
action_53 (80) = happyShift action_42
action_53 (81) = happyShift action_43
action_53 (82) = happyShift action_21
action_53 (23) = happyGoto action_26
action_53 (39) = happyGoto action_97
action_53 (40) = happyGoto action_28
action_53 (41) = happyGoto action_29
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (44) = happyShift action_31
action_54 (51) = happyShift action_32
action_54 (52) = happyShift action_33
action_54 (60) = happyShift action_34
action_54 (66) = happyShift action_35
action_54 (68) = happyShift action_36
action_54 (73) = happyShift action_37
action_54 (74) = happyShift action_38
action_54 (75) = happyShift action_39
action_54 (76) = happyShift action_40
action_54 (77) = happyShift action_41
action_54 (80) = happyShift action_42
action_54 (81) = happyShift action_43
action_54 (82) = happyShift action_21
action_54 (23) = happyGoto action_26
action_54 (39) = happyGoto action_96
action_54 (40) = happyGoto action_28
action_54 (41) = happyGoto action_29
action_54 _ = happyFail (happyExpListPerState 54)

action_55 (82) = happyShift action_21
action_55 (23) = happyGoto action_95
action_55 _ = happyFail (happyExpListPerState 55)

action_56 (82) = happyShift action_21
action_56 (23) = happyGoto action_94
action_56 _ = happyFail (happyExpListPerState 56)

action_57 (82) = happyShift action_21
action_57 (23) = happyGoto action_93
action_57 _ = happyFail (happyExpListPerState 57)

action_58 (56) = happyShift action_92
action_58 _ = happyFail (happyExpListPerState 58)

action_59 (83) = happyAccept
action_59 _ = happyFail (happyExpListPerState 59)

action_60 (49) = happyShift action_91
action_60 _ = happyFail (happyExpListPerState 60)

action_61 (83) = happyAccept
action_61 _ = happyFail (happyExpListPerState 61)

action_62 (82) = happyShift action_21
action_62 (23) = happyGoto action_90
action_62 _ = happyFail (happyExpListPerState 62)

action_63 (83) = happyAccept
action_63 _ = happyFail (happyExpListPerState 63)

action_64 (44) = happyShift action_66
action_64 (31) = happyGoto action_64
action_64 (32) = happyGoto action_89
action_64 _ = happyReduce_32

action_65 (83) = happyAccept
action_65 _ = happyFail (happyExpListPerState 65)

action_66 (82) = happyShift action_21
action_66 (23) = happyGoto action_88
action_66 _ = happyFail (happyExpListPerState 66)

action_67 (83) = happyAccept
action_67 _ = happyFail (happyExpListPerState 67)

action_68 (83) = happyAccept
action_68 _ = happyFail (happyExpListPerState 68)

action_69 (82) = happyShift action_21
action_69 (23) = happyGoto action_87
action_69 _ = happyFail (happyExpListPerState 69)

action_70 (59) = happyShift action_72
action_70 (28) = happyGoto action_70
action_70 (29) = happyGoto action_86
action_70 _ = happyReduce_28

action_71 (83) = happyAccept
action_71 _ = happyFail (happyExpListPerState 71)

action_72 (82) = happyShift action_21
action_72 (23) = happyGoto action_85
action_72 _ = happyFail (happyExpListPerState 72)

action_73 (83) = happyAccept
action_73 _ = happyFail (happyExpListPerState 73)

action_74 (83) = happyAccept
action_74 _ = happyFail (happyExpListPerState 74)

action_75 (82) = happyShift action_21
action_75 (23) = happyGoto action_84
action_75 _ = happyFail (happyExpListPerState 75)

action_76 (83) = happyAccept
action_76 _ = happyFail (happyExpListPerState 76)

action_77 _ = happyReduce_24

action_78 _ = happyReduce_25

action_79 (83) = happyAccept
action_79 _ = happyFail (happyExpListPerState 79)

action_80 (61) = happyShift action_75
action_80 (67) = happyShift action_69
action_80 (25) = happyGoto action_83
action_80 (26) = happyGoto action_80
action_80 (27) = happyGoto action_77
action_80 (30) = happyGoto action_78
action_80 _ = happyReduce_22

action_81 (83) = happyAccept
action_81 _ = happyFail (happyExpListPerState 81)

action_82 _ = happyReduce_21

action_83 _ = happyReduce_23

action_84 (59) = happyShift action_72
action_84 (28) = happyGoto action_70
action_84 (29) = happyGoto action_138
action_84 _ = happyReduce_28

action_85 _ = happyReduce_27

action_86 _ = happyReduce_29

action_87 (44) = happyShift action_66
action_87 (31) = happyGoto action_64
action_87 (32) = happyGoto action_137
action_87 _ = happyReduce_32

action_88 (47) = happyShift action_136
action_88 _ = happyFail (happyExpListPerState 88)

action_89 _ = happyReduce_33

action_90 _ = happyReduce_34

action_91 (57) = happyShift action_62
action_91 (33) = happyGoto action_60
action_91 (34) = happyGoto action_135
action_91 _ = happyReduce_35

action_92 (82) = happyShift action_21
action_92 (23) = happyGoto action_134
action_92 _ = happyFail (happyExpListPerState 92)

action_93 _ = happyReduce_40

action_94 (69) = happyShift action_133
action_94 _ = happyFail (happyExpListPerState 94)

action_95 (64) = happyShift action_50
action_95 (37) = happyGoto action_132
action_95 _ = happyReduce_46

action_96 _ = happyReduce_42

action_97 (47) = happyShift action_131
action_97 _ = happyFail (happyExpListPerState 97)

action_98 (54) = happyShift action_53
action_98 (55) = happyShift action_54
action_98 (56) = happyShift action_55
action_98 (62) = happyShift action_56
action_98 (63) = happyShift action_57
action_98 (65) = happyShift action_58
action_98 (35) = happyGoto action_51
action_98 (36) = happyGoto action_130
action_98 _ = happyReduce_43

action_99 (82) = happyShift action_21
action_99 (23) = happyGoto action_47
action_99 (38) = happyGoto action_129
action_99 _ = happyReduce_48

action_100 (82) = happyShift action_21
action_100 (23) = happyGoto action_47
action_100 (38) = happyGoto action_128
action_100 _ = happyReduce_48

action_101 _ = happyReduce_58

action_102 _ = happyReduce_61

action_103 _ = happyReduce_60

action_104 (79) = happyShift action_127
action_104 _ = happyFail (happyExpListPerState 104)

action_105 (44) = happyShift action_24
action_105 (53) = happyShift action_25
action_105 (82) = happyShift action_21
action_105 (23) = happyGoto action_22
action_105 (43) = happyGoto action_126
action_105 _ = happyFail (happyExpListPerState 105)

action_106 (44) = happyShift action_24
action_106 (53) = happyShift action_25
action_106 (82) = happyShift action_21
action_106 (23) = happyGoto action_22
action_106 (43) = happyGoto action_125
action_106 _ = happyFail (happyExpListPerState 106)

action_107 (44) = happyShift action_31
action_107 (51) = happyShift action_32
action_107 (52) = happyShift action_33
action_107 (60) = happyShift action_34
action_107 (66) = happyShift action_35
action_107 (68) = happyShift action_36
action_107 (73) = happyShift action_37
action_107 (74) = happyShift action_38
action_107 (75) = happyShift action_39
action_107 (76) = happyShift action_40
action_107 (77) = happyShift action_41
action_107 (80) = happyShift action_42
action_107 (81) = happyShift action_43
action_107 (82) = happyShift action_21
action_107 (23) = happyGoto action_26
action_107 (39) = happyGoto action_124
action_107 (40) = happyGoto action_28
action_107 (41) = happyGoto action_29
action_107 _ = happyFail (happyExpListPerState 107)

action_108 (50) = happyShift action_123
action_108 _ = happyFail (happyExpListPerState 108)

action_109 (44) = happyShift action_31
action_109 (51) = happyShift action_32
action_109 (52) = happyShift action_33
action_109 (60) = happyShift action_34
action_109 (66) = happyShift action_35
action_109 (68) = happyShift action_36
action_109 (73) = happyShift action_37
action_109 (74) = happyShift action_38
action_109 (75) = happyShift action_39
action_109 (76) = happyShift action_40
action_109 (77) = happyShift action_41
action_109 (80) = happyShift action_42
action_109 (81) = happyShift action_43
action_109 (82) = happyShift action_21
action_109 (23) = happyGoto action_26
action_109 (39) = happyGoto action_122
action_109 (40) = happyGoto action_28
action_109 (41) = happyGoto action_29
action_109 _ = happyFail (happyExpListPerState 109)

action_110 (44) = happyShift action_31
action_110 (51) = happyShift action_32
action_110 (52) = happyShift action_33
action_110 (60) = happyShift action_34
action_110 (66) = happyShift action_35
action_110 (68) = happyShift action_36
action_110 (73) = happyShift action_37
action_110 (74) = happyShift action_38
action_110 (75) = happyShift action_39
action_110 (76) = happyShift action_40
action_110 (77) = happyShift action_41
action_110 (80) = happyShift action_42
action_110 (81) = happyShift action_43
action_110 (82) = happyShift action_21
action_110 (23) = happyGoto action_26
action_110 (39) = happyGoto action_121
action_110 (40) = happyGoto action_28
action_110 (41) = happyGoto action_29
action_110 _ = happyFail (happyExpListPerState 110)

action_111 (45) = happyShift action_118
action_111 (46) = happyShift action_119
action_111 (47) = happyShift action_120
action_111 _ = happyFail (happyExpListPerState 111)

action_112 (44) = happyShift action_31
action_112 (51) = happyShift action_32
action_112 (52) = happyShift action_33
action_112 (60) = happyShift action_34
action_112 (66) = happyShift action_35
action_112 (68) = happyShift action_36
action_112 (73) = happyShift action_37
action_112 (74) = happyShift action_38
action_112 (75) = happyShift action_39
action_112 (76) = happyShift action_40
action_112 (77) = happyShift action_41
action_112 (80) = happyShift action_42
action_112 (81) = happyShift action_43
action_112 (82) = happyShift action_21
action_112 (23) = happyGoto action_26
action_112 (39) = happyGoto action_117
action_112 (40) = happyGoto action_28
action_112 (41) = happyGoto action_29
action_112 _ = happyFail (happyExpListPerState 112)

action_113 (44) = happyShift action_31
action_113 (51) = happyShift action_32
action_113 (52) = happyShift action_33
action_113 (60) = happyShift action_34
action_113 (66) = happyShift action_35
action_113 (68) = happyShift action_36
action_113 (73) = happyShift action_37
action_113 (74) = happyShift action_38
action_113 (75) = happyShift action_39
action_113 (76) = happyShift action_40
action_113 (77) = happyShift action_41
action_113 (80) = happyShift action_42
action_113 (81) = happyShift action_43
action_113 (82) = happyShift action_21
action_113 (23) = happyGoto action_26
action_113 (39) = happyGoto action_116
action_113 (40) = happyGoto action_28
action_113 (41) = happyGoto action_29
action_113 _ = happyFail (happyExpListPerState 113)

action_114 (46) = happyShift action_115
action_114 _ = happyFail (happyExpListPerState 114)

action_115 (44) = happyShift action_24
action_115 (53) = happyShift action_25
action_115 (82) = happyShift action_21
action_115 (23) = happyGoto action_22
action_115 (43) = happyGoto action_156
action_115 _ = happyFail (happyExpListPerState 115)

action_116 _ = happyReduce_55

action_117 _ = happyReduce_56

action_118 _ = happyReduce_71

action_119 (44) = happyShift action_31
action_119 (51) = happyShift action_32
action_119 (52) = happyShift action_33
action_119 (60) = happyShift action_34
action_119 (66) = happyShift action_35
action_119 (68) = happyShift action_36
action_119 (73) = happyShift action_37
action_119 (74) = happyShift action_38
action_119 (75) = happyShift action_39
action_119 (76) = happyShift action_40
action_119 (77) = happyShift action_41
action_119 (80) = happyShift action_42
action_119 (81) = happyShift action_43
action_119 (82) = happyShift action_21
action_119 (23) = happyGoto action_26
action_119 (39) = happyGoto action_155
action_119 (40) = happyGoto action_28
action_119 (41) = happyGoto action_29
action_119 _ = happyFail (happyExpListPerState 119)

action_120 (44) = happyShift action_31
action_120 (51) = happyShift action_32
action_120 (52) = happyShift action_33
action_120 (60) = happyShift action_34
action_120 (66) = happyShift action_35
action_120 (68) = happyShift action_36
action_120 (73) = happyShift action_37
action_120 (74) = happyShift action_38
action_120 (75) = happyShift action_39
action_120 (76) = happyShift action_40
action_120 (77) = happyShift action_41
action_120 (80) = happyShift action_42
action_120 (81) = happyShift action_43
action_120 (82) = happyShift action_21
action_120 (23) = happyGoto action_26
action_120 (39) = happyGoto action_154
action_120 (40) = happyGoto action_28
action_120 (41) = happyGoto action_29
action_120 _ = happyFail (happyExpListPerState 120)

action_121 (46) = happyShift action_153
action_121 _ = happyFail (happyExpListPerState 121)

action_122 (46) = happyShift action_152
action_122 _ = happyFail (happyExpListPerState 122)

action_123 (44) = happyShift action_31
action_123 (51) = happyShift action_32
action_123 (52) = happyShift action_33
action_123 (60) = happyShift action_34
action_123 (66) = happyShift action_35
action_123 (68) = happyShift action_36
action_123 (73) = happyShift action_37
action_123 (74) = happyShift action_38
action_123 (75) = happyShift action_39
action_123 (76) = happyShift action_40
action_123 (77) = happyShift action_41
action_123 (80) = happyShift action_42
action_123 (81) = happyShift action_43
action_123 (82) = happyShift action_21
action_123 (23) = happyGoto action_26
action_123 (39) = happyGoto action_151
action_123 (40) = happyGoto action_28
action_123 (41) = happyGoto action_29
action_123 _ = happyFail (happyExpListPerState 123)

action_124 (45) = happyShift action_150
action_124 _ = happyFail (happyExpListPerState 124)

action_125 (47) = happyShift action_149
action_125 _ = happyFail (happyExpListPerState 125)

action_126 (47) = happyShift action_148
action_126 _ = happyFail (happyExpListPerState 126)

action_127 (44) = happyShift action_31
action_127 (51) = happyShift action_32
action_127 (52) = happyShift action_33
action_127 (60) = happyShift action_34
action_127 (66) = happyShift action_35
action_127 (68) = happyShift action_36
action_127 (73) = happyShift action_37
action_127 (74) = happyShift action_38
action_127 (75) = happyShift action_39
action_127 (76) = happyShift action_40
action_127 (77) = happyShift action_41
action_127 (80) = happyShift action_42
action_127 (81) = happyShift action_43
action_127 (82) = happyShift action_21
action_127 (23) = happyGoto action_26
action_127 (39) = happyGoto action_27
action_127 (40) = happyGoto action_28
action_127 (41) = happyGoto action_29
action_127 (42) = happyGoto action_147
action_127 _ = happyFail (happyExpListPerState 127)

action_128 _ = happyReduce_50

action_129 (45) = happyShift action_146
action_129 _ = happyFail (happyExpListPerState 129)

action_130 _ = happyReduce_45

action_131 (44) = happyShift action_31
action_131 (51) = happyShift action_32
action_131 (52) = happyShift action_33
action_131 (60) = happyShift action_34
action_131 (66) = happyShift action_35
action_131 (68) = happyShift action_36
action_131 (73) = happyShift action_37
action_131 (74) = happyShift action_38
action_131 (75) = happyShift action_39
action_131 (76) = happyShift action_40
action_131 (77) = happyShift action_41
action_131 (80) = happyShift action_42
action_131 (81) = happyShift action_43
action_131 (82) = happyShift action_21
action_131 (23) = happyGoto action_26
action_131 (39) = happyGoto action_145
action_131 (40) = happyGoto action_28
action_131 (41) = happyGoto action_29
action_131 _ = happyFail (happyExpListPerState 131)

action_132 (47) = happyShift action_144
action_132 _ = happyFail (happyExpListPerState 132)

action_133 (70) = happyShift action_143
action_133 _ = happyFail (happyExpListPerState 133)

action_134 (64) = happyShift action_50
action_134 (37) = happyGoto action_142
action_134 _ = happyReduce_46

action_135 _ = happyReduce_36

action_136 (44) = happyShift action_31
action_136 (51) = happyShift action_32
action_136 (52) = happyShift action_33
action_136 (60) = happyShift action_34
action_136 (66) = happyShift action_35
action_136 (68) = happyShift action_36
action_136 (73) = happyShift action_37
action_136 (74) = happyShift action_38
action_136 (75) = happyShift action_39
action_136 (76) = happyShift action_40
action_136 (77) = happyShift action_41
action_136 (80) = happyShift action_42
action_136 (81) = happyShift action_43
action_136 (82) = happyShift action_21
action_136 (23) = happyGoto action_26
action_136 (39) = happyGoto action_141
action_136 (40) = happyGoto action_28
action_136 (41) = happyGoto action_29
action_136 _ = happyFail (happyExpListPerState 136)

action_137 (49) = happyShift action_140
action_137 _ = happyFail (happyExpListPerState 137)

action_138 (44) = happyShift action_66
action_138 (31) = happyGoto action_64
action_138 (32) = happyGoto action_139
action_138 _ = happyReduce_32

action_139 (49) = happyShift action_169
action_139 _ = happyFail (happyExpListPerState 139)

action_140 _ = happyReduce_30

action_141 (45) = happyShift action_168
action_141 _ = happyFail (happyExpListPerState 141)

action_142 (47) = happyShift action_167
action_142 _ = happyFail (happyExpListPerState 142)

action_143 (54) = happyShift action_53
action_143 (55) = happyShift action_54
action_143 (56) = happyShift action_55
action_143 (62) = happyShift action_56
action_143 (63) = happyShift action_57
action_143 (65) = happyShift action_58
action_143 (35) = happyGoto action_51
action_143 (36) = happyGoto action_166
action_143 _ = happyReduce_43

action_144 (44) = happyShift action_31
action_144 (51) = happyShift action_32
action_144 (52) = happyShift action_33
action_144 (60) = happyShift action_34
action_144 (66) = happyShift action_35
action_144 (68) = happyShift action_36
action_144 (73) = happyShift action_37
action_144 (74) = happyShift action_38
action_144 (75) = happyShift action_39
action_144 (76) = happyShift action_40
action_144 (77) = happyShift action_41
action_144 (80) = happyShift action_42
action_144 (81) = happyShift action_43
action_144 (82) = happyShift action_21
action_144 (23) = happyGoto action_26
action_144 (39) = happyGoto action_165
action_144 (40) = happyGoto action_28
action_144 (41) = happyGoto action_29
action_144 _ = happyFail (happyExpListPerState 144)

action_145 _ = happyReduce_41

action_146 _ = happyReduce_47

action_147 _ = happyReduce_53

action_148 (44) = happyShift action_31
action_148 (51) = happyShift action_32
action_148 (52) = happyShift action_33
action_148 (60) = happyShift action_34
action_148 (66) = happyShift action_35
action_148 (68) = happyShift action_36
action_148 (73) = happyShift action_37
action_148 (74) = happyShift action_38
action_148 (75) = happyShift action_39
action_148 (76) = happyShift action_40
action_148 (77) = happyShift action_41
action_148 (80) = happyShift action_42
action_148 (81) = happyShift action_43
action_148 (82) = happyShift action_21
action_148 (23) = happyGoto action_26
action_148 (39) = happyGoto action_164
action_148 (40) = happyGoto action_28
action_148 (41) = happyGoto action_29
action_148 _ = happyFail (happyExpListPerState 148)

action_149 (44) = happyShift action_31
action_149 (51) = happyShift action_32
action_149 (52) = happyShift action_33
action_149 (60) = happyShift action_34
action_149 (66) = happyShift action_35
action_149 (68) = happyShift action_36
action_149 (73) = happyShift action_37
action_149 (74) = happyShift action_38
action_149 (75) = happyShift action_39
action_149 (76) = happyShift action_40
action_149 (77) = happyShift action_41
action_149 (80) = happyShift action_42
action_149 (81) = happyShift action_43
action_149 (82) = happyShift action_21
action_149 (23) = happyGoto action_26
action_149 (39) = happyGoto action_163
action_149 (40) = happyGoto action_28
action_149 (41) = happyGoto action_29
action_149 _ = happyFail (happyExpListPerState 149)

action_150 _ = happyReduce_67

action_151 (58) = happyShift action_162
action_151 _ = happyFail (happyExpListPerState 151)

action_152 (44) = happyShift action_31
action_152 (51) = happyShift action_32
action_152 (52) = happyShift action_33
action_152 (60) = happyShift action_34
action_152 (66) = happyShift action_35
action_152 (68) = happyShift action_36
action_152 (73) = happyShift action_37
action_152 (74) = happyShift action_38
action_152 (75) = happyShift action_39
action_152 (76) = happyShift action_40
action_152 (77) = happyShift action_41
action_152 (80) = happyShift action_42
action_152 (81) = happyShift action_43
action_152 (82) = happyShift action_21
action_152 (23) = happyGoto action_26
action_152 (39) = happyGoto action_161
action_152 (40) = happyGoto action_28
action_152 (41) = happyGoto action_29
action_152 _ = happyFail (happyExpListPerState 152)

action_153 (44) = happyShift action_31
action_153 (51) = happyShift action_32
action_153 (52) = happyShift action_33
action_153 (60) = happyShift action_34
action_153 (66) = happyShift action_35
action_153 (68) = happyShift action_36
action_153 (73) = happyShift action_37
action_153 (74) = happyShift action_38
action_153 (75) = happyShift action_39
action_153 (76) = happyShift action_40
action_153 (77) = happyShift action_41
action_153 (80) = happyShift action_42
action_153 (81) = happyShift action_43
action_153 (82) = happyShift action_21
action_153 (23) = happyGoto action_26
action_153 (39) = happyGoto action_160
action_153 (40) = happyGoto action_28
action_153 (41) = happyGoto action_29
action_153 _ = happyFail (happyExpListPerState 153)

action_154 (45) = happyShift action_159
action_154 _ = happyFail (happyExpListPerState 154)

action_155 (45) = happyShift action_158
action_155 _ = happyFail (happyExpListPerState 155)

action_156 (45) = happyShift action_157
action_156 _ = happyFail (happyExpListPerState 156)

action_157 _ = happyReduce_75

action_158 _ = happyReduce_69

action_159 _ = happyReduce_70

action_160 (46) = happyShift action_178
action_160 _ = happyFail (happyExpListPerState 160)

action_161 (46) = happyShift action_177
action_161 _ = happyFail (happyExpListPerState 161)

action_162 (44) = happyShift action_31
action_162 (51) = happyShift action_32
action_162 (52) = happyShift action_33
action_162 (60) = happyShift action_34
action_162 (66) = happyShift action_35
action_162 (68) = happyShift action_36
action_162 (73) = happyShift action_37
action_162 (74) = happyShift action_38
action_162 (75) = happyShift action_39
action_162 (76) = happyShift action_40
action_162 (77) = happyShift action_41
action_162 (80) = happyShift action_42
action_162 (81) = happyShift action_43
action_162 (82) = happyShift action_21
action_162 (23) = happyGoto action_26
action_162 (39) = happyGoto action_27
action_162 (40) = happyGoto action_28
action_162 (41) = happyGoto action_29
action_162 (42) = happyGoto action_176
action_162 _ = happyFail (happyExpListPerState 162)

action_163 (45) = happyShift action_175
action_163 _ = happyFail (happyExpListPerState 163)

action_164 (45) = happyShift action_174
action_164 _ = happyFail (happyExpListPerState 164)

action_165 (48) = happyShift action_173
action_165 _ = happyFail (happyExpListPerState 165)

action_166 (71) = happyShift action_172
action_166 _ = happyFail (happyExpListPerState 166)

action_167 (44) = happyShift action_31
action_167 (51) = happyShift action_32
action_167 (52) = happyShift action_33
action_167 (60) = happyShift action_34
action_167 (66) = happyShift action_35
action_167 (68) = happyShift action_36
action_167 (73) = happyShift action_37
action_167 (74) = happyShift action_38
action_167 (75) = happyShift action_39
action_167 (76) = happyShift action_40
action_167 (77) = happyShift action_41
action_167 (80) = happyShift action_42
action_167 (81) = happyShift action_43
action_167 (82) = happyShift action_21
action_167 (23) = happyGoto action_26
action_167 (39) = happyGoto action_171
action_167 (40) = happyGoto action_28
action_167 (41) = happyGoto action_29
action_167 _ = happyFail (happyExpListPerState 167)

action_168 _ = happyReduce_31

action_169 (57) = happyShift action_62
action_169 (33) = happyGoto action_60
action_169 (34) = happyGoto action_170
action_169 _ = happyReduce_35

action_170 (54) = happyShift action_53
action_170 (55) = happyShift action_54
action_170 (56) = happyShift action_55
action_170 (62) = happyShift action_56
action_170 (63) = happyShift action_57
action_170 (65) = happyShift action_58
action_170 (35) = happyGoto action_51
action_170 (36) = happyGoto action_185
action_170 _ = happyReduce_43

action_171 (48) = happyShift action_184
action_171 _ = happyFail (happyExpListPerState 171)

action_172 _ = happyReduce_39

action_173 (44) = happyShift action_31
action_173 (51) = happyShift action_32
action_173 (52) = happyShift action_33
action_173 (60) = happyShift action_34
action_173 (66) = happyShift action_35
action_173 (68) = happyShift action_36
action_173 (73) = happyShift action_37
action_173 (74) = happyShift action_38
action_173 (75) = happyShift action_39
action_173 (76) = happyShift action_40
action_173 (77) = happyShift action_41
action_173 (80) = happyShift action_42
action_173 (81) = happyShift action_43
action_173 (82) = happyShift action_21
action_173 (23) = happyGoto action_26
action_173 (39) = happyGoto action_183
action_173 (40) = happyGoto action_28
action_173 (41) = happyGoto action_29
action_173 _ = happyFail (happyExpListPerState 173)

action_174 (72) = happyShift action_182
action_174 _ = happyFail (happyExpListPerState 174)

action_175 (78) = happyShift action_181
action_175 _ = happyFail (happyExpListPerState 175)

action_176 _ = happyReduce_54

action_177 (44) = happyShift action_31
action_177 (51) = happyShift action_32
action_177 (52) = happyShift action_33
action_177 (60) = happyShift action_34
action_177 (66) = happyShift action_35
action_177 (68) = happyShift action_36
action_177 (73) = happyShift action_37
action_177 (74) = happyShift action_38
action_177 (75) = happyShift action_39
action_177 (76) = happyShift action_40
action_177 (77) = happyShift action_41
action_177 (80) = happyShift action_42
action_177 (81) = happyShift action_43
action_177 (82) = happyShift action_21
action_177 (23) = happyGoto action_26
action_177 (39) = happyGoto action_180
action_177 (40) = happyGoto action_28
action_177 (41) = happyGoto action_29
action_177 _ = happyFail (happyExpListPerState 177)

action_178 (44) = happyShift action_31
action_178 (51) = happyShift action_32
action_178 (52) = happyShift action_33
action_178 (60) = happyShift action_34
action_178 (66) = happyShift action_35
action_178 (68) = happyShift action_36
action_178 (73) = happyShift action_37
action_178 (74) = happyShift action_38
action_178 (75) = happyShift action_39
action_178 (76) = happyShift action_40
action_178 (77) = happyShift action_41
action_178 (80) = happyShift action_42
action_178 (81) = happyShift action_43
action_178 (82) = happyShift action_21
action_178 (23) = happyGoto action_26
action_178 (39) = happyGoto action_179
action_178 (40) = happyGoto action_28
action_178 (41) = happyGoto action_29
action_178 _ = happyFail (happyExpListPerState 178)

action_179 (45) = happyShift action_190
action_179 _ = happyFail (happyExpListPerState 179)

action_180 (45) = happyShift action_189
action_180 _ = happyFail (happyExpListPerState 180)

action_181 (44) = happyShift action_31
action_181 (51) = happyShift action_32
action_181 (52) = happyShift action_33
action_181 (60) = happyShift action_34
action_181 (66) = happyShift action_35
action_181 (68) = happyShift action_36
action_181 (73) = happyShift action_37
action_181 (74) = happyShift action_38
action_181 (75) = happyShift action_39
action_181 (76) = happyShift action_40
action_181 (77) = happyShift action_41
action_181 (80) = happyShift action_42
action_181 (81) = happyShift action_43
action_181 (82) = happyShift action_21
action_181 (23) = happyGoto action_26
action_181 (39) = happyGoto action_27
action_181 (40) = happyGoto action_28
action_181 (41) = happyGoto action_29
action_181 (42) = happyGoto action_188
action_181 _ = happyFail (happyExpListPerState 181)

action_182 (44) = happyShift action_31
action_182 (51) = happyShift action_32
action_182 (52) = happyShift action_33
action_182 (60) = happyShift action_34
action_182 (66) = happyShift action_35
action_182 (68) = happyShift action_36
action_182 (73) = happyShift action_37
action_182 (74) = happyShift action_38
action_182 (75) = happyShift action_39
action_182 (76) = happyShift action_40
action_182 (77) = happyShift action_41
action_182 (80) = happyShift action_42
action_182 (81) = happyShift action_43
action_182 (82) = happyShift action_21
action_182 (23) = happyGoto action_26
action_182 (39) = happyGoto action_27
action_182 (40) = happyGoto action_28
action_182 (41) = happyGoto action_29
action_182 (42) = happyGoto action_187
action_182 _ = happyFail (happyExpListPerState 182)

action_183 _ = happyReduce_37

action_184 (44) = happyShift action_31
action_184 (51) = happyShift action_32
action_184 (52) = happyShift action_33
action_184 (60) = happyShift action_34
action_184 (66) = happyShift action_35
action_184 (68) = happyShift action_36
action_184 (73) = happyShift action_37
action_184 (74) = happyShift action_38
action_184 (75) = happyShift action_39
action_184 (76) = happyShift action_40
action_184 (77) = happyShift action_41
action_184 (80) = happyShift action_42
action_184 (81) = happyShift action_43
action_184 (82) = happyShift action_21
action_184 (23) = happyGoto action_26
action_184 (39) = happyGoto action_186
action_184 (40) = happyGoto action_28
action_184 (41) = happyGoto action_29
action_184 _ = happyFail (happyExpListPerState 184)

action_185 _ = happyReduce_26

action_186 _ = happyReduce_38

action_187 _ = happyReduce_52

action_188 _ = happyReduce_51

action_189 _ = happyReduce_68

action_190 _ = happyReduce_66

happyReduce_20 = happySpecReduce_1  23 happyReduction_20
happyReduction_20 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.VarIdent (tokenText happy_var_1))
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  24 happyReduction_21
happyReduction_21 (HappyAbsSyn25  happy_var_1)
	 =  HappyAbsSyn24
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AProgram (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_0  25 happyReduction_22
happyReduction_22  =  HappyAbsSyn25
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_23 = happySpecReduce_2  25 happyReduction_23
happyReduction_23 (HappyAbsSyn25  happy_var_2)
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn25
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_23 _ _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_1  26 happyReduction_24
happyReduction_24 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn26
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.UnitModule (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_24 _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_1  26 happyReduction_25
happyReduction_25 (HappyAbsSyn30  happy_var_1)
	 =  HappyAbsSyn26
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.UnitTelescope (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_25 _  = notHappyAtAll 

happyReduce_26 = happyReduce 7 27 happyReduction_26
happyReduction_26 ((HappyAbsSyn36  happy_var_7) `HappyStk`
	(HappyAbsSyn34  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_4) `HappyStk`
	(HappyAbsSyn29  happy_var_3) `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AModule (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_27 = happySpecReduce_2  28 happyReduction_27
happyReduction_27 (HappyAbsSyn23  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn28
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnInclude (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_27 _ _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_0  29 happyReduction_28
happyReduction_28  =  HappyAbsSyn29
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_29 = happySpecReduce_2  29 happyReduction_29
happyReduction_29 (HappyAbsSyn29  happy_var_2)
	(HappyAbsSyn28  happy_var_1)
	 =  HappyAbsSyn29
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_29 _ _  = notHappyAtAll 

happyReduce_30 = happyReduce 4 30 happyReduction_30
happyReduction_30 (_ `HappyStk`
	(HappyAbsSyn32  happy_var_3) `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn30
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.ATelescope (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 5 31 happyReduction_31
happyReduction_31 (_ `HappyStk`
	(HappyAbsSyn39  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AParam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_32 = happySpecReduce_0  32 happyReduction_32
happyReduction_32  =  HappyAbsSyn32
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_33 = happySpecReduce_2  32 happyReduction_33
happyReduction_33 (HappyAbsSyn32  happy_var_2)
	(HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn32
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_33 _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_2  33 happyReduction_34
happyReduction_34 (HappyAbsSyn23  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn33
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnImport (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_34 _ _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_0  34 happyReduction_35
happyReduction_35  =  HappyAbsSyn34
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_36 = happySpecReduce_3  34 happyReduction_36
happyReduction_36 (HappyAbsSyn34  happy_var_3)
	_
	(HappyAbsSyn33  happy_var_1)
	 =  HappyAbsSyn34
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_36 _ _ _  = notHappyAtAll 

happyReduce_37 = happyReduce 7 35 happyReduction_37
happyReduction_37 ((HappyAbsSyn39  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn37  happy_var_3) `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn35
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_38 = happyReduce 8 35 happyReduction_38
happyReduction_38 ((HappyAbsSyn39  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn37  happy_var_4) `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn35
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclPrivateDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_39 = happyReduce 6 35 happyReduction_39
happyReduction_39 (_ `HappyStk`
	(HappyAbsSyn36  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn35
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclNamespace (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_5))
	) `HappyStk` happyRest

happyReduce_40 = happySpecReduce_2  35 happyReduction_40
happyReduction_40 (HappyAbsSyn23  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn35
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclOpen (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_40 _ _  = notHappyAtAll 

happyReduce_41 = happyReduce 4 35 happyReduction_41
happyReduction_41 ((HappyAbsSyn39  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn35
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCheck (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_42 = happySpecReduce_2  35 happyReduction_42
happyReduction_42 (HappyAbsSyn39  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn35
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCompute (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_42 _ _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_0  36 happyReduction_43
happyReduction_43  =  HappyAbsSyn36
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_44 = happySpecReduce_1  36 happyReduction_44
happyReduction_44 (HappyAbsSyn35  happy_var_1)
	 =  HappyAbsSyn36
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_44 _  = notHappyAtAll 

happyReduce_45 = happySpecReduce_3  36 happyReduction_45
happyReduction_45 (HappyAbsSyn36  happy_var_3)
	_
	(HappyAbsSyn35  happy_var_1)
	 =  HappyAbsSyn36
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_45 _ _ _  = notHappyAtAll 

happyReduce_46 = happySpecReduce_0  37 happyReduction_46
happyReduction_46  =  HappyAbsSyn37
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, Language.MLTT.Syntax.Abs.NoDischarge Language.MLTT.Syntax.Abs.BNFC'NoPosition)
	)

happyReduce_47 = happyReduce 4 37 happyReduction_47
happyReduction_47 (_ `HappyStk`
	(HappyAbsSyn38  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn37
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DischargeOver (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_48 = happySpecReduce_0  38 happyReduction_48
happyReduction_48  =  HappyAbsSyn38
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_49 = happySpecReduce_1  38 happyReduction_49
happyReduction_49 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn38
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_49 _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_3  38 happyReduction_50
happyReduction_50 (HappyAbsSyn38  happy_var_3)
	_
	(HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn38
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_50 _ _ _  = notHappyAtAll 

happyReduce_51 = happyReduce 8 39 happyReduction_51
happyReduction_51 ((HappyAbsSyn42  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pi (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_52 = happyReduce 8 39 happyReduction_52
happyReduction_52 ((HappyAbsSyn42  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Sigma (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_53 = happyReduce 4 39 happyReduction_53
happyReduction_53 ((HappyAbsSyn42  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Lam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_54 = happyReduce 6 39 happyReduction_54
happyReduction_54 ((HappyAbsSyn42  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Let (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_55 = happySpecReduce_3  39 happyReduction_55
happyReduction_55 (HappyAbsSyn39  happy_var_3)
	_
	(HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn39
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Arrow (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_55 _ _ _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_3  39 happyReduction_56
happyReduction_56 (HappyAbsSyn39  happy_var_3)
	_
	(HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn39
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Product (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_56 _ _ _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_1  39 happyReduction_57
happyReduction_57 (HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn39
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_57 _  = notHappyAtAll 

happyReduce_58 = happySpecReduce_2  40 happyReduction_58
happyReduction_58 (HappyAbsSyn39  happy_var_2)
	(HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn39
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.App (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_58 _ _  = notHappyAtAll 

happyReduce_59 = happySpecReduce_1  40 happyReduction_59
happyReduction_59 (HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn39
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_59 _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_2  41 happyReduction_60
happyReduction_60 (HappyAbsSyn39  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.First (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_60 _ _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_2  41 happyReduction_61
happyReduction_61 (HappyAbsSyn39  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Second (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_61 _ _  = notHappyAtAll 

happyReduce_62 = happySpecReduce_1  41 happyReduction_62
happyReduction_62 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Universe (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_62 _  = notHappyAtAll 

happyReduce_63 = happySpecReduce_1  41 happyReduction_63
happyReduction_63 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_63 _  = notHappyAtAll 

happyReduce_64 = happySpecReduce_1  41 happyReduction_64
happyReduction_64 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitVal (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_64 _  = notHappyAtAll 

happyReduce_65 = happySpecReduce_1  41 happyReduction_65
happyReduction_65 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn39
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Var (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_65 _  = notHappyAtAll 

happyReduce_66 = happyReduce 8 41 happyReduction_66
happyReduction_66 (_ `HappyStk`
	(HappyAbsSyn39  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.IdType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_67 = happyReduce 4 41 happyReduction_67
happyReduction_67 (_ `HappyStk`
	(HappyAbsSyn39  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Refl (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_68 = happyReduce 8 41 happyReduction_68
happyReduction_68 (_ `HappyStk`
	(HappyAbsSyn39  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.J (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_69 = happyReduce 5 41 happyReduction_69
happyReduction_69 (_ `HappyStk`
	(HappyAbsSyn39  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_70 = happyReduce 5 41 happyReduction_70
happyReduction_70 (_ `HappyStk`
	(HappyAbsSyn39  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Ann (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_71 = happySpecReduce_3  41 happyReduction_71
happyReduction_71 _
	(HappyAbsSyn39  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)
happyReduction_71 _ _ _  = notHappyAtAll 

happyReduce_72 = happySpecReduce_1  42 happyReduction_72
happyReduction_72 (HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn42
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AScopedTerm (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_72 _  = notHappyAtAll 

happyReduce_73 = happySpecReduce_1  43 happyReduction_73
happyReduction_73 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn43
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternWildcard (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_73 _  = notHappyAtAll 

happyReduce_74 = happySpecReduce_1  43 happyReduction_74
happyReduction_74 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn43
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.PatternVar (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_74 _  = notHappyAtAll 

happyReduce_75 = happyReduce 5 43 happyReduction_75
happyReduction_75 (_ `HappyStk`
	(HappyAbsSyn43  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn43
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternPair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 83 83 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 44;
	PT _ (TS _ 2) -> cont 45;
	PT _ (TS _ 3) -> cont 46;
	PT _ (TS _ 4) -> cont 47;
	PT _ (TS _ 5) -> cont 48;
	PT _ (TS _ 6) -> cont 49;
	PT _ (TS _ 7) -> cont 50;
	PT _ (TS _ 8) -> cont 51;
	PT _ (TS _ 9) -> cont 52;
	PT _ (TS _ 10) -> cont 53;
	PT _ (TS _ 11) -> cont 54;
	PT _ (TS _ 12) -> cont 55;
	PT _ (TS _ 13) -> cont 56;
	PT _ (TS _ 14) -> cont 57;
	PT _ (TS _ 15) -> cont 58;
	PT _ (TS _ 16) -> cont 59;
	PT _ (TS _ 17) -> cont 60;
	PT _ (TS _ 18) -> cont 61;
	PT _ (TS _ 19) -> cont 62;
	PT _ (TS _ 20) -> cont 63;
	PT _ (TS _ 21) -> cont 64;
	PT _ (TS _ 22) -> cont 65;
	PT _ (TS _ 23) -> cont 66;
	PT _ (TS _ 24) -> cont 67;
	PT _ (TS _ 25) -> cont 68;
	PT _ (TS _ 26) -> cont 69;
	PT _ (TS _ 27) -> cont 70;
	PT _ (TS _ 28) -> cont 71;
	PT _ (TS _ 29) -> cont 72;
	PT _ (TS _ 30) -> cont 73;
	PT _ (TS _ 31) -> cont 74;
	PT _ (TS _ 32) -> cont 75;
	PT _ (TS _ 33) -> cont 76;
	PT _ (TS _ 34) -> cont 77;
	PT _ (TS _ 35) -> cont 78;
	PT _ (TS _ 36) -> cont 79;
	PT _ (TS _ 37) -> cont 80;
	PT _ (TS _ 38) -> cont 81;
	PT _ (T_VarIdent _) -> cont 82;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 83 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = ((>>=))
happyReturn :: () => a -> Err a
happyReturn = (return)
happyThen1 m k tks = ((>>=)) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pProgram_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn24 z -> happyReturn z; _other -> notHappyAtAll })

pListUnit_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn25 z -> happyReturn z; _other -> notHappyAtAll })

pUnit_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn26 z -> happyReturn z; _other -> notHappyAtAll })

pModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn27 z -> happyReturn z; _other -> notHappyAtAll })

pInclude_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn28 z -> happyReturn z; _other -> notHappyAtAll })

pListInclude_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn29 z -> happyReturn z; _other -> notHappyAtAll })

pTelescopeDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn30 z -> happyReturn z; _other -> notHappyAtAll })

pParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_7 tks) (\x -> case x of {HappyAbsSyn31 z -> happyReturn z; _other -> notHappyAtAll })

pListParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_8 tks) (\x -> case x of {HappyAbsSyn32 z -> happyReturn z; _other -> notHappyAtAll })

pImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_9 tks) (\x -> case x of {HappyAbsSyn33 z -> happyReturn z; _other -> notHappyAtAll })

pListImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_10 tks) (\x -> case x of {HappyAbsSyn34 z -> happyReturn z; _other -> notHappyAtAll })

pDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_11 tks) (\x -> case x of {HappyAbsSyn35 z -> happyReturn z; _other -> notHappyAtAll })

pListDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_12 tks) (\x -> case x of {HappyAbsSyn36 z -> happyReturn z; _other -> notHappyAtAll })

pDischarge_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_13 tks) (\x -> case x of {HappyAbsSyn37 z -> happyReturn z; _other -> notHappyAtAll })

pListVarIdent_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_14 tks) (\x -> case x of {HappyAbsSyn38 z -> happyReturn z; _other -> notHappyAtAll })

pTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_15 tks) (\x -> case x of {HappyAbsSyn39 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_16 tks) (\x -> case x of {HappyAbsSyn39 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_17 tks) (\x -> case x of {HappyAbsSyn39 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_18 tks) (\x -> case x of {HappyAbsSyn42 z -> happyReturn z; _other -> notHappyAtAll })

pPattern_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_19 tks) (\x -> case x of {HappyAbsSyn43 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

-- Entrypoints

pProgram :: [Token] -> Err Language.MLTT.Syntax.Abs.Program
pProgram = fmap snd . pProgram_internal

pListUnit :: [Token] -> Err [Language.MLTT.Syntax.Abs.Unit]
pListUnit = fmap snd . pListUnit_internal

pUnit :: [Token] -> Err Language.MLTT.Syntax.Abs.Unit
pUnit = fmap snd . pUnit_internal

pModule :: [Token] -> Err Language.MLTT.Syntax.Abs.Module
pModule = fmap snd . pModule_internal

pInclude :: [Token] -> Err Language.MLTT.Syntax.Abs.Include
pInclude = fmap snd . pInclude_internal

pListInclude :: [Token] -> Err [Language.MLTT.Syntax.Abs.Include]
pListInclude = fmap snd . pListInclude_internal

pTelescopeDecl :: [Token] -> Err Language.MLTT.Syntax.Abs.TelescopeDecl
pTelescopeDecl = fmap snd . pTelescopeDecl_internal

pParam :: [Token] -> Err Language.MLTT.Syntax.Abs.Param
pParam = fmap snd . pParam_internal

pListParam :: [Token] -> Err [Language.MLTT.Syntax.Abs.Param]
pListParam = fmap snd . pListParam_internal

pImport :: [Token] -> Err Language.MLTT.Syntax.Abs.Import
pImport = fmap snd . pImport_internal

pListImport :: [Token] -> Err [Language.MLTT.Syntax.Abs.Import]
pListImport = fmap snd . pListImport_internal

pDecl :: [Token] -> Err Language.MLTT.Syntax.Abs.Decl
pDecl = fmap snd . pDecl_internal

pListDecl :: [Token] -> Err [Language.MLTT.Syntax.Abs.Decl]
pListDecl = fmap snd . pListDecl_internal

pDischarge :: [Token] -> Err Language.MLTT.Syntax.Abs.Discharge
pDischarge = fmap snd . pDischarge_internal

pListVarIdent :: [Token] -> Err [Language.MLTT.Syntax.Abs.VarIdent]
pListVarIdent = fmap snd . pListVarIdent_internal

pTerm :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm = fmap snd . pTerm_internal

pTerm1 :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm1 = fmap snd . pTerm1_internal

pTerm2 :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm2 = fmap snd . pTerm2_internal

pScopedTerm :: [Token] -> Err Language.MLTT.Syntax.Abs.ScopedTerm
pScopedTerm = fmap snd . pScopedTerm_internal

pPattern :: [Token] -> Err Language.MLTT.Syntax.Abs.Pattern
pPattern = fmap snd . pPattern_internal
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Prelude.Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x Prelude.< y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Prelude.Int ->                    -- token number
         Prelude.Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Prelude.- ((1) :: Prelude.Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Prelude.Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n Prelude.- ((1) :: Prelude.Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Prelude.- ((1)::Prelude.Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
