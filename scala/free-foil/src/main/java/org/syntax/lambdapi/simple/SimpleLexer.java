// Generated from org/syntax/lambdapi/simple/SimpleLexer.g4 by ANTLR 4.9.3
package org.syntax.lambdapi.simple;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SimpleLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.9.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		Surrogate_id_SYMB_0=1, Surrogate_id_SYMB_1=2, Surrogate_id_SYMB_2=3, Surrogate_id_SYMB_3=4, 
		Surrogate_id_SYMB_4=5, Surrogate_id_SYMB_5=6, Surrogate_id_SYMB_6=7, Surrogate_id_SYMB_7=8, 
		Surrogate_id_SYMB_8=9, Surrogate_id_SYMB_9=10, COMMENT_antlr_builtin=11, 
		MULTICOMMENT_antlr_builtin=12, IDENT=13, WS=14, ErrorToken=15;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"LETTER", "CAPITAL", "SMALL", "DIGIT", "Surrogate_id_SYMB_0", "Surrogate_id_SYMB_1", 
			"Surrogate_id_SYMB_2", "Surrogate_id_SYMB_3", "Surrogate_id_SYMB_4", 
			"Surrogate_id_SYMB_5", "Surrogate_id_SYMB_6", "Surrogate_id_SYMB_7", 
			"Surrogate_id_SYMB_8", "Surrogate_id_SYMB_9", "COMMENT_antlr_builtin", 
			"MULTICOMMENT_antlr_builtin", "IDENTIFIER_FIRST", "IDENT", "WS", "Escapable", 
			"ErrorToken"
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


	public SimpleLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "SimpleLexer.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\21\u008c\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\3\2\3\2\5\2\60\n\2\3\3\3"+
		"\3\3\4\3\4\3\5\3\5\3\6\3\6\3\7\3\7\3\b\3\b\3\t\3\t\3\n\3\n\3\13\3\13\3"+
		"\f\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\16\3\16\3\17"+
		"\3\17\3\20\3\20\3\20\3\20\7\20Z\n\20\f\20\16\20]\13\20\3\20\5\20`\n\20"+
		"\3\20\3\20\5\20d\n\20\3\20\3\20\3\21\3\21\3\21\3\21\7\21l\n\21\f\21\16"+
		"\21o\13\21\3\21\3\21\3\21\3\21\3\21\3\22\3\22\5\22x\n\22\3\23\3\23\3\23"+
		"\7\23}\n\23\f\23\16\23\u0080\13\23\3\24\6\24\u0083\n\24\r\24\16\24\u0084"+
		"\3\24\3\24\3\25\3\25\3\26\3\26\3m\2\27\3\2\5\2\7\2\t\2\13\3\r\4\17\5\21"+
		"\6\23\7\25\b\27\t\31\n\33\13\35\f\37\r!\16#\2%\17\'\20)\2+\21\3\2\b\5"+
		"\2C\\\u00c2\u00d8\u00da\u00e0\5\2c|\u00e1\u00f8\u00fa\u0101\3\2\62;\4"+
		"\2\f\f\17\17\5\2\13\f\16\17\"\"\b\2$$^^hhppttvv\2\u008e\2\13\3\2\2\2\2"+
		"\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3"+
		"\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2"+
		"\2%\3\2\2\2\2\'\3\2\2\2\2+\3\2\2\2\3/\3\2\2\2\5\61\3\2\2\2\7\63\3\2\2"+
		"\2\t\65\3\2\2\2\13\67\3\2\2\2\r9\3\2\2\2\17;\3\2\2\2\21=\3\2\2\2\23?\3"+
		"\2\2\2\25A\3\2\2\2\27C\3\2\2\2\31I\3\2\2\2\33Q\3\2\2\2\35S\3\2\2\2\37"+
		"U\3\2\2\2!g\3\2\2\2#w\3\2\2\2%y\3\2\2\2\'\u0082\3\2\2\2)\u0088\3\2\2\2"+
		"+\u008a\3\2\2\2-\60\5\5\3\2.\60\5\7\4\2/-\3\2\2\2/.\3\2\2\2\60\4\3\2\2"+
		"\2\61\62\t\2\2\2\62\6\3\2\2\2\63\64\t\3\2\2\64\b\3\2\2\2\65\66\t\4\2\2"+
		"\66\n\3\2\2\2\678\7<\2\28\f\3\2\2\29:\7=\2\2:\16\3\2\2\2;<\7\60\2\2<\20"+
		"\3\2\2\2=>\7*\2\2>\22\3\2\2\2?@\7+\2\2@\24\3\2\2\2AB\7\u2194\2\2B\26\3"+
		"\2\2\2CD\7e\2\2DE\7j\2\2EF\7g\2\2FG\7e\2\2GH\7m\2\2H\30\3\2\2\2IJ\7e\2"+
		"\2JK\7q\2\2KL\7o\2\2LM\7r\2\2MN\7w\2\2NO\7v\2\2OP\7g\2\2P\32\3\2\2\2Q"+
		"R\7\u03a2\2\2R\34\3\2\2\2ST\7\u03bd\2\2T\36\3\2\2\2UV\7/\2\2VW\7/\2\2"+
		"W[\3\2\2\2XZ\n\5\2\2YX\3\2\2\2Z]\3\2\2\2[Y\3\2\2\2[\\\3\2\2\2\\c\3\2\2"+
		"\2][\3\2\2\2^`\7\17\2\2_^\3\2\2\2_`\3\2\2\2`a\3\2\2\2ad\7\f\2\2bd\7\2"+
		"\2\3c_\3\2\2\2cb\3\2\2\2de\3\2\2\2ef\b\20\2\2f \3\2\2\2gh\7}\2\2hi\7/"+
		"\2\2im\3\2\2\2jl\13\2\2\2kj\3\2\2\2lo\3\2\2\2mn\3\2\2\2mk\3\2\2\2np\3"+
		"\2\2\2om\3\2\2\2pq\7/\2\2qr\7\177\2\2rs\3\2\2\2st\b\21\2\2t\"\3\2\2\2"+
		"ux\5\3\2\2vx\7a\2\2wu\3\2\2\2wv\3\2\2\2x$\3\2\2\2y~\5#\22\2z}\5#\22\2"+
		"{}\5\t\5\2|z\3\2\2\2|{\3\2\2\2}\u0080\3\2\2\2~|\3\2\2\2~\177\3\2\2\2\177"+
		"&\3\2\2\2\u0080~\3\2\2\2\u0081\u0083\t\6\2\2\u0082\u0081\3\2\2\2\u0083"+
		"\u0084\3\2\2\2\u0084\u0082\3\2\2\2\u0084\u0085\3\2\2\2\u0085\u0086\3\2"+
		"\2\2\u0086\u0087\b\24\2\2\u0087(\3\2\2\2\u0088\u0089\t\7\2\2\u0089*\3"+
		"\2\2\2\u008a\u008b\13\2\2\2\u008b,\3\2\2\2\f\2/[_cmw|~\u0084\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}