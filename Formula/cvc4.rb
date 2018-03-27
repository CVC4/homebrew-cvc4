class Cvc4 < Formula
  desc "Open-source automatic theorem prover for SMT"
  homepage "https://cvc4.cs.stanford.edu/"
  url "https://cvc4.cs.stanford.edu/downloads/builds/src/cvc4-1.5.tar.gz"
  sha256 "5d6b4f8ee8420f85e3f804181341cedf6ea32342c48f355a5be87754152b14e9"
  version "1.5"

  option "with-java-bindings", "Compile with Java bindings"

  depends_on "boost" => :build
  depends_on "coreutils" => :build
  depends_on "python3" => :build
  depends_on "gmp"
  depends_on :java if build.with? "java-bindings"
  depends_on "swig@2" => :build if build.with? "java-bindings"
  depends_on "autoconf" => :build if build.devel?
  depends_on "automake" => :build if build.devel?
  depends_on "libtool" => :build if build.devel?
  depends_on :arch => :x86_64

  def install
    args = ["--enable-static",
            "--enable-shared",
            "--with-compat",
            "--bsd",
            "--with-gmp",
            "--with-antlr-dir=#{buildpath}/antlr-3.4",
            "ANTLR=#{buildpath}/antlr-3.4/bin/antlr3",
            "--prefix=#{prefix}"]

    if build.with? "java-bindings"
      args << "--enable-language-bindings=java"
      args << "CFLAGS=-I/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/System/Library/Frameworks/JavaVM.framework/Versions/A/Headers/"
      args << "CXXFLAGS=-I/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/System/Library/Frameworks/JavaVM.framework/Versions/A/Headers/"
    end

    system "contrib/get-antlr-3.4"
    system "./autogen.sh" if build.devel?
    system "./configure", *args
    system "make", "install"
  end

  devel do
    url "https://github.com/CVC4/CVC4/archive/master.zip"
    version "1.6"
  end

  test do
    (testpath/"simple.cvc").write <<~EOS
      x0, x1, x2, x3 : BOOLEAN;
      ASSERT x1 OR NOT x0;
      ASSERT x0 OR NOT x3;
      ASSERT x3 OR x2;
      ASSERT x1 AND NOT x1;
      % EXPECT: valid
      QUERY x2;
    EOS
    result = shell_output "#{bin}/cvc4 #{(testpath/"simple.cvc")}"
    assert_match /valid/, result
    (testpath/"simple.smt").write <<~EOS
      (set-option :produce-models true)
      (set-logic QF_BV)
      (define-fun s_2 () Bool false)
      (define-fun s_1 () Bool true)
      (assert (not s_1))
      (check-sat)
    EOS
    result = shell_output "#{bin}/cvc4 --lang smt #{(testpath/"simple.smt")}"
    assert_match /unsat/, result
  end
end
