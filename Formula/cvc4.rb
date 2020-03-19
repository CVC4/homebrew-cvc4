class Cvc4 < Formula
  include Language::Python::Virtualenv

  desc "Open-source automatic theorem prover for SMT"
  homepage "https://cvc4.cs.stanford.edu/"
  url "https://github.com/CVC4/CVC4/archive/1.7.tar.gz"
  sha256 "9864a364a0076ef7ff63a46cdbc69cbe6568604149626338598d4df7788f8c2e"
  head "https://github.com/CVC4/CVC4.git"

  option "with-java-bindings", "Compile with Java bindings"
  option "with-gpl", "Allow building against GPL'ed libraries"

  depends_on "coreutils" => :build
  depends_on "cmake" => :build
  depends_on "python" => :build
  depends_on "gmp"
  depends_on "readline" => :optional
  depends_on :java if build.with? "java-bindings"
  depends_on "swig"
  depends_on "automake" => :build if not build.head?
  depends_on "libtool" => :build if not build.head?
  depends_on "cryptominisat" => :build
  depends_on :arch => :x86_64

  resource "toml" do
    url "https://files.pythonhosted.org/packages/b9/19/5cbd78eac8b1783671c40e34bb0fa83133a06d340a38b55c645076d40094/toml-0.10.0.tar.gz"
    sha256 "229f81c57791a41d65e399fc06bf0848bab550a9dfd5ed66df18ce5f05e73d5c"
  end

  def run_in_venv(venv, cmd)
    cmd = ["source", "#{venv}/bin/activate", "&&"] + Shellwords.join(cmd)
    system "bash", "-c", cmd

  def install
    system "contrib/get-antlr-3.4"
    system "contrib/get-symfpu"

    args = ["--prefix=#{prefix}",
            "--symfpu",
            "--cryptominisat",
            "--python3"]

    venv_root = "#{buildpath}/venv"
    if build.head?
      venv = virtualenv_create(venv_root, "python3")
      venv.pip_install resources
    end

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

    if build.head?
      run_in_venv(venv_root, ["./configure.sh", *args])
      chdir "build" do
        run_in_venv(venv_root, ["make", "install"])
      end
    else
      system "./configure.sh", *args
      chdir "build" do
        system "make", "install"
      end
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
