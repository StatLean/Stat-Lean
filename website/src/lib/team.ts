export interface Member {
  name: string;
  role: string;
  department: string;
  university: string;
  homepage?: string;
  /** filename under public/team/ */
  photo: string;
}

export const MEMBERS: Member[] = [
  {
    name: "Junwei Lu",
    role: "Associate Professor",
    department: "Department of Biostatistics",
    university: "Harvard T.H. Chan School of Public Health",
    homepage: "https://junwei-lu.github.io/",
    photo: "Junwei_Lu.jpeg",
  },
  {
    name: "Ethan X. Fang",
    role: "Associate Professor",
    department: "Department of Biostatistics & Bioinformatics",
    university: "Duke University",
    homepage: "https://ethanfangduke.github.io/",
    photo: "Ethan_Fang.jpg",
  },
  {
    name: "Tingzhou Wei",
    role: "Graduate Student",
    department: "Department of Biostatistics & Bioinformatics",
    university: "Duke University",
    photo: "Tingzhou_Wei.jpg",
  },
  {
    name: "Zeyu Zheng",
    role: "Graduate Student",
    department: "Department of Mathematical Sciences",
    university: "Carnegie Mellon University",
    homepage: "https://zeyu-zheng.github.io/",
    photo: "Zeyu_Zheng.jpg",
  },
];
