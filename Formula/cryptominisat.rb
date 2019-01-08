class Cryptominisat < Formula
  desc "An advanced SAT solver"
  homepage "https://www.msoos.org/"
  url "https://github.com/msoos/cryptominisat/archive/5.6.6.tar.gz"
  sha256 "95fac3df4311d4fb6e2674b1bce3113056795a2eda51cd807f73bcc4f9b1a2d5"

  depends_on "boost" => :recommended
  depends_on "cmake" => :build
  depends_on "python" => :recommended
  depends_on "zlib" => :recommended
  depends_on :arch => :x86_64

  def install
    args = ["-DCMAKE_INSTALL_PREFIX=#{prefix}",
            "-DNOM4RI=ON"]

    if not build.with? "python"
      args << "--DENABLE_PYTHON_INTERFACE=OFF"
    end

    mkdir "build" do
      system "cmake", *args, ".."
      system "make", "install"
    end
  end
end
