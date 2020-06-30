class AntlrAT3 < Formula
  desc "Antlr3 has a C API which has been dropped in Antlr4"
  homepage "http://www.antlr.org/"
  url "https://www.antlr3.org/download/antlr-3.4-complete.jar"
  sha256 "9d3e866b610460664522520f73b81777b5626fb0a282a5952b9800b751550bf7"

  depends_on :java

  def install
    libexec.install "antlr-3.4-complete.jar"
    (share+"java").install_symlink "#{libexec}/antlr-3.4-complete.jar" => "antlr3.jar"
    (bin+"antlr3").write <<~EOS
      #!/bin/sh
      java -jar #{libexec}/antlr-3.4-complete.jar "$@"
    EOS
  end

  test do
    exppath = testpath/"Exp.g"
    exppath.write <<~EOS
      grammar Exp;
      eval returns [double value]
          :    exp=atomExp {$value = $exp.value;}
          ;
      atomExp returns [double value]
          :    n=Number                {$value = Double.parseDouble($n.text);}
          ;
      Number
          :    ('0'..'9')+ ('.' ('0'..'9')+)?
          ;
      WS
          :   (' ' | '\\t' | '\\r'| '\\n') {\$channel=HIDDEN;}
          ;
    EOS
    javapath = testpath/"ANTLRDemo.java"
    javapath.write <<~EOS
      import org.antlr.runtime.*;
      public class ANTLRDemo {
          public static void main(String[] args) throws Exception {
              ANTLRStringStream in = new ANTLRStringStream("42");
              ExpLexer lexer = new ExpLexer(in);
              CommonTokenStream tokens = new CommonTokenStream(lexer);
              ExpParser parser = new ExpParser(tokens);
              System.out.println(parser.eval()); // print the value
          }
      }
    EOS
    ENV.prepend "CLASSPATH", "#{share}/java/antlr3.jar", ":"
    ENV.prepend "CLASSPATH", ".", ":"
    system "#{bin}/antlr3", "Exp.g"
    system "javac", "ANTLRDemo.java"
    assert_match("42.0", pipe_output("java ANTLRDemo"))
  end
end
