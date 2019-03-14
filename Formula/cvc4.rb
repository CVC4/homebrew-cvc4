class Cvc4 < Formula
  desc "Open-source automatic theorem prover for SMT"
  homepage "https://cvc4.cs.stanford.edu/"
  url "https://cvc4.cs.stanford.edu/downloads/builds/src/cvc4-1.6.tar.gz"
  sha256 "5c18bd5ea893fba9723a4d35c889d412ec6d29a21db9db69481891a8ff4887c7"
  head "https://github.com/CVC4/CVC4.git"

  option "with-java-bindings", "Compile with Java bindings"
  option "with-gpl", "Allow building against GPL'ed libraries"

  depends_on "boost" => :build
  depends_on "coreutils" => :build
  depends_on "cmake" => :build if build.head?
  depends_on "python" => :build
  depends_on "gmp"
  depends_on "readline" => :optional
  depends_on :java if build.with? "java-bindings"
  depends_on "swig"
  depends_on "automake" => :build if not build.head?
  depends_on "libtool" => :build if not build.head?
  # wget is required for the 1.6 release because it lacks the fix for following
  # redirects when using cURL:
  # https://github.com/CVC4/CVC4/commit/fc07d6af4156fde8af048ca5db8ff1f43de48ebc
  depends_on "wget" => :build if not build.head?
  depends_on "cryptominisat"
  depends_on :arch => :x86_64

  def install
    system "contrib/get-antlr-3.4"
    system "contrib/get-symfpu"
    system "contrib/get-lfsc-checker"
    system "contrib/get-cadical"

    if build.head?
      args = ["--prefix=#{prefix}",
              "--symfpu",
              "--cryptominisat",
              "--lfsc",
              "--cadical"]

      if build.with? "java-bindings"
        args << "--language-bindings=java"
      end

      if allow_gpl?
        args << "--gpl"
      end

      if build.with? "readline"
        gpl_dependency "readline"
        args << "--readline"
      end

      system "./configure.sh", *args
      chdir "build" do
        system "make", "install"
      end
    else
      args = ["--enable-static",
              "--enable-shared",
              "--with-compat",
              allow_gpl? ? "--enable-gpl" : "--bsd",
              "--with-gmp",
              "--prefix=#{prefix}",
              "--with-symfpu",
              "--with-cryptominisat",
              "--with-lfsc",
              "--with-cadical"]

      if build.with? "java-bindings"
        args << "--enable-language-bindings=java"
        args << "CFLAGS=-I/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/System/Library/Frameworks/JavaVM.framework/Versions/A/Headers/"
        args << "CXXFLAGS=-I/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/System/Library/Frameworks/JavaVM.framework/Versions/A/Headers/"
      end

      if build.with? "readline"
        gpl_dependency "readline"
        args << "--with-readline"
      end

      system "./configure", *args
      system "make", "install"
    end
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

  private

  def allow_gpl?
    build.with?("gpl")
  end

  def gpl_dependency(dep)
    odie "--with-gpl is required to build with #{dep}" unless allow_gpl?
  end
end
