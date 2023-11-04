// Generated from org/syntax/lambdapi/simple/SimpleParser.g4 by ANTLR 4.9.3
package org.syntax.lambdapi.simple;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SimpleParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.9.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		Surrogate_id_SYMB_0=1, Surrogate_id_SYMB_1=2, Surrogate_id_SYMB_2=3, Surrogate_id_SYMB_3=4, 
		Surrogate_id_SYMB_4=5, Surrogate_id_SYMB_5=6, Surrogate_id_SYMB_6=7, Surrogate_id_SYMB_7=8, 
		Surrogate_id_SYMB_8=9, Surrogate_id_SYMB_9=10, COMMENT_antlr_builtin=11, 
		MULTICOMMENT_antlr_builtin=12, IDENT=13, WS=14, ErrorToken=15;
	public static final int
		RULE_start_Program = 0, RULE_start_Command = 1, RULE_start_ListCommand = 2, 
		RULE_start_Term = 3, RULE_start_Term1 = 4, RULE_start_Term2 = 5, RULE_program = 6, 
		RULE_command = 7, RULE_listCommand = 8, RULE_term = 9, RULE_term1 = 10, 
		RULE_term2 = 11;
	private static String[] makeRuleNames() {
		return new String[] {
			"start_Program", "start_Command", "start_ListCommand", "start_Term", 
			"start_Term1", "start_Term2", "program", "command", "listCommand", "term", 
			"term1", "term2"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "':'", "';'", "'.'", "'('", "')'", "'\u2192'", "'check'", "'compute'", 
			"'\u03A0'", "'\u03BB'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "Surrogate_id_SYMB_0", "Surrogate_id_SYMB_1", "Surrogate_id_SYMB_2", 
			"Surrogate_id_SYMB_3", "Surrogate_id_SYMB_4", "Surrogate_id_SYMB_5", 
			"Surrogate_id_SYMB_6", "Surrogate_id_SYMB_7", "Surrogate_id_SYMB_8", 
			"Surrogate_id_SYMB_9", "COMMENT_antlr_builtin", "MULTICOMMENT_antlr_builtin", 
			"IDENT", "WS", "ErrorToken"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "SimpleParser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public SimpleParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class Start_ProgramContext extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Program result;
		public ProgramContext x;
		public TerminalNode EOF() { return getToken(SimpleParser.EOF, 0); }
		public ProgramContext program() {
			return getRuleContext(ProgramContext.class,0);
		}
		public Start_ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Program; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterStart_Program(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitStart_Program(this);
		}
	}

	public final Start_ProgramContext start_Program() throws RecognitionException {
		Start_ProgramContext _localctx = new Start_ProgramContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_start_Program);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(24);
			((Start_ProgramContext)_localctx).x = program();
			setState(25);
			match(EOF);
			 ((Start_ProgramContext)_localctx).result =  ((Start_ProgramContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_CommandContext extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Command result;
		public CommandContext x;
		public TerminalNode EOF() { return getToken(SimpleParser.EOF, 0); }
		public CommandContext command() {
			return getRuleContext(CommandContext.class,0);
		}
		public Start_CommandContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Command; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterStart_Command(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitStart_Command(this);
		}
	}

	public final Start_CommandContext start_Command() throws RecognitionException {
		Start_CommandContext _localctx = new Start_CommandContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_start_Command);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(28);
			((Start_CommandContext)_localctx).x = command();
			setState(29);
			match(EOF);
			 ((Start_CommandContext)_localctx).result =  ((Start_CommandContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_ListCommandContext extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.ListCommand result;
		public ListCommandContext x;
		public TerminalNode EOF() { return getToken(SimpleParser.EOF, 0); }
		public ListCommandContext listCommand() {
			return getRuleContext(ListCommandContext.class,0);
		}
		public Start_ListCommandContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_ListCommand; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterStart_ListCommand(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitStart_ListCommand(this);
		}
	}

	public final Start_ListCommandContext start_ListCommand() throws RecognitionException {
		Start_ListCommandContext _localctx = new Start_ListCommandContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_start_ListCommand);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(32);
			((Start_ListCommandContext)_localctx).x = listCommand(0);
			setState(33);
			match(EOF);
			 ((Start_ListCommandContext)_localctx).result =  ((Start_ListCommandContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_TermContext extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Term result;
		public TermContext x;
		public TerminalNode EOF() { return getToken(SimpleParser.EOF, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public Start_TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Term; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterStart_Term(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitStart_Term(this);
		}
	}

	public final Start_TermContext start_Term() throws RecognitionException {
		Start_TermContext _localctx = new Start_TermContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_start_Term);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(36);
			((Start_TermContext)_localctx).x = term();
			setState(37);
			match(EOF);
			 ((Start_TermContext)_localctx).result =  ((Start_TermContext)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Term1Context extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Term result;
		public Term1Context x;
		public TerminalNode EOF() { return getToken(SimpleParser.EOF, 0); }
		public Term1Context term1() {
			return getRuleContext(Term1Context.class,0);
		}
		public Start_Term1Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Term1; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterStart_Term1(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitStart_Term1(this);
		}
	}

	public final Start_Term1Context start_Term1() throws RecognitionException {
		Start_Term1Context _localctx = new Start_Term1Context(_ctx, getState());
		enterRule(_localctx, 8, RULE_start_Term1);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(40);
			((Start_Term1Context)_localctx).x = term1(0);
			setState(41);
			match(EOF);
			 ((Start_Term1Context)_localctx).result =  ((Start_Term1Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Start_Term2Context extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Term result;
		public Term2Context x;
		public TerminalNode EOF() { return getToken(SimpleParser.EOF, 0); }
		public Term2Context term2() {
			return getRuleContext(Term2Context.class,0);
		}
		public Start_Term2Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start_Term2; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterStart_Term2(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitStart_Term2(this);
		}
	}

	public final Start_Term2Context start_Term2() throws RecognitionException {
		Start_Term2Context _localctx = new Start_Term2Context(_ctx, getState());
		enterRule(_localctx, 10, RULE_start_Term2);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(44);
			((Start_Term2Context)_localctx).x = term2();
			setState(45);
			match(EOF);
			 ((Start_Term2Context)_localctx).result =  ((Start_Term2Context)_localctx).x.result; 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ProgramContext extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Program result;
		public ListCommandContext p_1_1;
		public ListCommandContext listCommand() {
			return getRuleContext(ListCommandContext.class,0);
		}
		public ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_program; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterProgram(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitProgram(this);
		}
	}

	public final ProgramContext program() throws RecognitionException {
		ProgramContext _localctx = new ProgramContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_program);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(48);
			((ProgramContext)_localctx).p_1_1 = listCommand(0);
			 ((ProgramContext)_localctx).result =  new org.syntax.lambdapi.simple.Absyn.AProgram(((ProgramContext)_localctx).p_1_1.result); 
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CommandContext extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Command result;
		public TermContext p_1_2;
		public TermContext p_1_4;
		public TermContext p_2_2;
		public TermContext p_2_4;
		public TerminalNode Surrogate_id_SYMB_6() { return getToken(SimpleParser.Surrogate_id_SYMB_6, 0); }
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(SimpleParser.Surrogate_id_SYMB_0, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_7() { return getToken(SimpleParser.Surrogate_id_SYMB_7, 0); }
		public CommandContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_command; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterCommand(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitCommand(this);
		}
	}

	public final CommandContext command() throws RecognitionException {
		CommandContext _localctx = new CommandContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_command);
		try {
			setState(63);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_6:
				enterOuterAlt(_localctx, 1);
				{
				setState(51);
				match(Surrogate_id_SYMB_6);
				setState(52);
				((CommandContext)_localctx).p_1_2 = term();
				setState(53);
				match(Surrogate_id_SYMB_0);
				setState(54);
				((CommandContext)_localctx).p_1_4 = term();
				 ((CommandContext)_localctx).result =  new org.syntax.lambdapi.simple.Absyn.CommandCheck(((CommandContext)_localctx).p_1_2.result,((CommandContext)_localctx).p_1_4.result); 
				}
				break;
			case Surrogate_id_SYMB_7:
				enterOuterAlt(_localctx, 2);
				{
				setState(57);
				match(Surrogate_id_SYMB_7);
				setState(58);
				((CommandContext)_localctx).p_2_2 = term();
				setState(59);
				match(Surrogate_id_SYMB_0);
				setState(60);
				((CommandContext)_localctx).p_2_4 = term();
				 ((CommandContext)_localctx).result =  new org.syntax.lambdapi.simple.Absyn.CommandCompute(((CommandContext)_localctx).p_2_2.result,((CommandContext)_localctx).p_2_4.result); 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ListCommandContext extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.ListCommand result;
		public ListCommandContext p_2_1;
		public CommandContext p_2_2;
		public TerminalNode Surrogate_id_SYMB_1() { return getToken(SimpleParser.Surrogate_id_SYMB_1, 0); }
		public ListCommandContext listCommand() {
			return getRuleContext(ListCommandContext.class,0);
		}
		public CommandContext command() {
			return getRuleContext(CommandContext.class,0);
		}
		public ListCommandContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_listCommand; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterListCommand(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitListCommand(this);
		}
	}

	public final ListCommandContext listCommand() throws RecognitionException {
		return listCommand(0);
	}

	private ListCommandContext listCommand(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ListCommandContext _localctx = new ListCommandContext(_ctx, _parentState);
		ListCommandContext _prevctx = _localctx;
		int _startState = 16;
		enterRecursionRule(_localctx, 16, RULE_listCommand, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			 ((ListCommandContext)_localctx).result =  new org.syntax.lambdapi.simple.Absyn.ListCommand(); 
			}
			_ctx.stop = _input.LT(-1);
			setState(75);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,1,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new ListCommandContext(_parentctx, _parentState);
					_localctx.p_2_1 = _prevctx;
					_localctx.p_2_1 = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_listCommand);
					setState(68);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(69);
					((ListCommandContext)_localctx).p_2_2 = command();
					setState(70);
					match(Surrogate_id_SYMB_1);
					 ((ListCommandContext)_localctx).result =  ((ListCommandContext)_localctx).p_2_1.result; _localctx.result.addLast(((ListCommandContext)_localctx).p_2_2.result); 
					}
					} 
				}
				setState(77);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,1,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class TermContext extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Term result;
		public Token p_1_2;
		public TermContext p_1_4;
		public Token p_2_3;
		public TermContext p_2_5;
		public TermContext p_2_8;
		public Term1Context p_3_1;
		public TerminalNode Surrogate_id_SYMB_9() { return getToken(SimpleParser.Surrogate_id_SYMB_9, 0); }
		public TerminalNode Surrogate_id_SYMB_2() { return getToken(SimpleParser.Surrogate_id_SYMB_2, 0); }
		public TerminalNode IDENT() { return getToken(SimpleParser.IDENT, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public TerminalNode Surrogate_id_SYMB_8() { return getToken(SimpleParser.Surrogate_id_SYMB_8, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(SimpleParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_0() { return getToken(SimpleParser.Surrogate_id_SYMB_0, 0); }
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(SimpleParser.Surrogate_id_SYMB_4, 0); }
		public TerminalNode Surrogate_id_SYMB_5() { return getToken(SimpleParser.Surrogate_id_SYMB_5, 0); }
		public Term1Context term1() {
			return getRuleContext(Term1Context.class,0);
		}
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterTerm(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitTerm(this);
		}
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_term);
		try {
			setState(97);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Surrogate_id_SYMB_9:
				enterOuterAlt(_localctx, 1);
				{
				setState(78);
				match(Surrogate_id_SYMB_9);
				setState(79);
				((TermContext)_localctx).p_1_2 = match(IDENT);
				setState(80);
				match(Surrogate_id_SYMB_2);
				setState(81);
				((TermContext)_localctx).p_1_4 = term();
				 ((TermContext)_localctx).result =  new org.syntax.lambdapi.simple.Absyn.Lam(((TermContext)_localctx).p_1_2.getText(),((TermContext)_localctx).p_1_4.result); 
				}
				break;
			case Surrogate_id_SYMB_8:
				enterOuterAlt(_localctx, 2);
				{
				setState(84);
				match(Surrogate_id_SYMB_8);
				setState(85);
				match(Surrogate_id_SYMB_3);
				setState(86);
				((TermContext)_localctx).p_2_3 = match(IDENT);
				setState(87);
				match(Surrogate_id_SYMB_0);
				setState(88);
				((TermContext)_localctx).p_2_5 = term();
				setState(89);
				match(Surrogate_id_SYMB_4);
				setState(90);
				match(Surrogate_id_SYMB_5);
				setState(91);
				((TermContext)_localctx).p_2_8 = term();
				 ((TermContext)_localctx).result =  new org.syntax.lambdapi.simple.Absyn.Pi(((TermContext)_localctx).p_2_3.getText(),((TermContext)_localctx).p_2_5.result,((TermContext)_localctx).p_2_8.result); 
				}
				break;
			case Surrogate_id_SYMB_3:
			case IDENT:
				enterOuterAlt(_localctx, 3);
				{
				setState(94);
				((TermContext)_localctx).p_3_1 = term1(0);
				 ((TermContext)_localctx).result =  ((TermContext)_localctx).p_3_1.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Term1Context extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Term result;
		public Term1Context p_1_1;
		public Term2Context p_2_1;
		public Term2Context p_1_2;
		public Term2Context term2() {
			return getRuleContext(Term2Context.class,0);
		}
		public Term1Context term1() {
			return getRuleContext(Term1Context.class,0);
		}
		public Term1Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term1; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterTerm1(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitTerm1(this);
		}
	}

	public final Term1Context term1() throws RecognitionException {
		return term1(0);
	}

	private Term1Context term1(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		Term1Context _localctx = new Term1Context(_ctx, _parentState);
		Term1Context _prevctx = _localctx;
		int _startState = 20;
		enterRecursionRule(_localctx, 20, RULE_term1, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(100);
			((Term1Context)_localctx).p_2_1 = term2();
			 ((Term1Context)_localctx).result =  ((Term1Context)_localctx).p_2_1.result; 
			}
			_ctx.stop = _input.LT(-1);
			setState(109);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new Term1Context(_parentctx, _parentState);
					_localctx.p_1_1 = _prevctx;
					_localctx.p_1_1 = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_term1);
					setState(103);
					if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
					setState(104);
					((Term1Context)_localctx).p_1_2 = term2();
					 ((Term1Context)_localctx).result =  new org.syntax.lambdapi.simple.Absyn.App(((Term1Context)_localctx).p_1_1.result,((Term1Context)_localctx).p_1_2.result); 
					}
					} 
				}
				setState(111);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class Term2Context extends ParserRuleContext {
		public org.syntax.lambdapi.simple.Absyn.Term result;
		public Token p_1_1;
		public TermContext p_2_2;
		public TerminalNode IDENT() { return getToken(SimpleParser.IDENT, 0); }
		public TerminalNode Surrogate_id_SYMB_3() { return getToken(SimpleParser.Surrogate_id_SYMB_3, 0); }
		public TerminalNode Surrogate_id_SYMB_4() { return getToken(SimpleParser.Surrogate_id_SYMB_4, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public Term2Context(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term2; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).enterTerm2(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SimpleParserListener ) ((SimpleParserListener)listener).exitTerm2(this);
		}
	}

	public final Term2Context term2() throws RecognitionException {
		Term2Context _localctx = new Term2Context(_ctx, getState());
		enterRule(_localctx, 22, RULE_term2);
		try {
			setState(119);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case IDENT:
				enterOuterAlt(_localctx, 1);
				{
				setState(112);
				((Term2Context)_localctx).p_1_1 = match(IDENT);
				 ((Term2Context)_localctx).result =  new org.syntax.lambdapi.simple.Absyn.Var(((Term2Context)_localctx).p_1_1.getText()); 
				}
				break;
			case Surrogate_id_SYMB_3:
				enterOuterAlt(_localctx, 2);
				{
				setState(114);
				match(Surrogate_id_SYMB_3);
				setState(115);
				((Term2Context)_localctx).p_2_2 = term();
				setState(116);
				match(Surrogate_id_SYMB_4);
				 ((Term2Context)_localctx).result =  ((Term2Context)_localctx).p_2_2.result; 
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 8:
			return listCommand_sempred((ListCommandContext)_localctx, predIndex);
		case 10:
			return term1_sempred((Term1Context)_localctx, predIndex);
		}
		return true;
	}
	private boolean listCommand_sempred(ListCommandContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 1);
		}
		return true;
	}
	private boolean term1_sempred(Term1Context _localctx, int predIndex) {
		switch (predIndex) {
		case 1:
			return precpred(_ctx, 2);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\21|\4\2\t\2\4\3\t"+
		"\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t\13\4"+
		"\f\t\f\4\r\t\r\3\2\3\2\3\2\3\2\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\5\3\5"+
		"\3\5\3\5\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\t\3\t\3\t\3\t\3"+
		"\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\5\tB\n\t\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3"+
		"\n\7\nL\n\n\f\n\16\nO\13\n\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13"+
		"\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\5\13d\n\13\3\f\3\f"+
		"\3\f\3\f\3\f\3\f\3\f\3\f\7\fn\n\f\f\f\16\fq\13\f\3\r\3\r\3\r\3\r\3\r\3"+
		"\r\3\r\5\rz\n\r\3\r\2\4\22\26\16\2\4\6\b\n\f\16\20\22\24\26\30\2\2\2u"+
		"\2\32\3\2\2\2\4\36\3\2\2\2\6\"\3\2\2\2\b&\3\2\2\2\n*\3\2\2\2\f.\3\2\2"+
		"\2\16\62\3\2\2\2\20A\3\2\2\2\22C\3\2\2\2\24c\3\2\2\2\26e\3\2\2\2\30y\3"+
		"\2\2\2\32\33\5\16\b\2\33\34\7\2\2\3\34\35\b\2\1\2\35\3\3\2\2\2\36\37\5"+
		"\20\t\2\37 \7\2\2\3 !\b\3\1\2!\5\3\2\2\2\"#\5\22\n\2#$\7\2\2\3$%\b\4\1"+
		"\2%\7\3\2\2\2&\'\5\24\13\2\'(\7\2\2\3()\b\5\1\2)\t\3\2\2\2*+\5\26\f\2"+
		"+,\7\2\2\3,-\b\6\1\2-\13\3\2\2\2./\5\30\r\2/\60\7\2\2\3\60\61\b\7\1\2"+
		"\61\r\3\2\2\2\62\63\5\22\n\2\63\64\b\b\1\2\64\17\3\2\2\2\65\66\7\t\2\2"+
		"\66\67\5\24\13\2\678\7\3\2\289\5\24\13\29:\b\t\1\2:B\3\2\2\2;<\7\n\2\2"+
		"<=\5\24\13\2=>\7\3\2\2>?\5\24\13\2?@\b\t\1\2@B\3\2\2\2A\65\3\2\2\2A;\3"+
		"\2\2\2B\21\3\2\2\2CD\b\n\1\2DE\b\n\1\2EM\3\2\2\2FG\f\3\2\2GH\5\20\t\2"+
		"HI\7\4\2\2IJ\b\n\1\2JL\3\2\2\2KF\3\2\2\2LO\3\2\2\2MK\3\2\2\2MN\3\2\2\2"+
		"N\23\3\2\2\2OM\3\2\2\2PQ\7\f\2\2QR\7\17\2\2RS\7\5\2\2ST\5\24\13\2TU\b"+
		"\13\1\2Ud\3\2\2\2VW\7\13\2\2WX\7\6\2\2XY\7\17\2\2YZ\7\3\2\2Z[\5\24\13"+
		"\2[\\\7\7\2\2\\]\7\b\2\2]^\5\24\13\2^_\b\13\1\2_d\3\2\2\2`a\5\26\f\2a"+
		"b\b\13\1\2bd\3\2\2\2cP\3\2\2\2cV\3\2\2\2c`\3\2\2\2d\25\3\2\2\2ef\b\f\1"+
		"\2fg\5\30\r\2gh\b\f\1\2ho\3\2\2\2ij\f\4\2\2jk\5\30\r\2kl\b\f\1\2ln\3\2"+
		"\2\2mi\3\2\2\2nq\3\2\2\2om\3\2\2\2op\3\2\2\2p\27\3\2\2\2qo\3\2\2\2rs\7"+
		"\17\2\2sz\b\r\1\2tu\7\6\2\2uv\5\24\13\2vw\7\7\2\2wx\b\r\1\2xz\3\2\2\2"+
		"yr\3\2\2\2yt\3\2\2\2z\31\3\2\2\2\7AMcoy";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}