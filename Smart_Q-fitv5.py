import tkinter as tk
from operator import index
from tkinter import filedialog, messagebox
from tkinter import ttk
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import pandas as pd
import numpy as np
import os
import tkinter.filedialog
import matplotlib.pyplot as plt
import math
from scipy.signal import find_peaks
import scipy.optimize as optimize
from scipy.ndimage import gaussian_filter1d
from scipy.signal import hilbert
from sklearn.metrics import r2_score
from numpy.fft import fft,ifft,fftshift,ifftshift
from matplotlib import cm
import csv
# 定义目标函数和其他辅助函数
def target_fun(x, a0, a1, a2, a3):
    f0 = (np.abs(a0 * (1 + a1 / (- (x - a3) * 1j - (a1 + a2) / 2)))) ** 2
    return f0

def delta_wl_to_f(delta_wl, wl_center):
    c0 = 3 * 10 ** 8
    delta_f = (10 ** -9) * c0 * (delta_wl * 10 ** -9) / ((wl_center * 10 ** -9) ** 2)
    return delta_f

import tkinter as tk
from tkinter import ttk
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import csv
import os

class Smart_Q_fit:
    def __init__(self, root):
        self.root = root
        self.root.title("Smart Q-fit")
        self.export = 0
        self.save_folder_path=""
        # 设置窗口大小
        self.root.geometry("1600x1000")
        self.peak_depth=tk.StringVar()
        self.peak_depth.set("0")
        self.peak_distance=tk.StringVar()
        self.peak_distance.set("500")
        self.peak_depth_var=0
        # 使用 ttk 主题
        self.style = ttk.Style()
        self.resonance_lw_var=tk.StringVar()
        self.resonance_lw_var.set("0.03")
        self.style.theme_use("clam")  # 可以选择其他主题如 'alt', 'default', 'vista'
        color1="#E5E9E4"
        root.config(bg=color1)
        # 设置所有控件的背景颜色
        color="#A2BDC9"
        self.style.configure("TButton", background=color)
        self.style.configure("TLabel", background=color1)
        self.style.configure("TFrame", background=color1)
        self.style.configure("TEntry", fieldbackground=color1, background="white")
        self.style.configure("TCheckbutton", background=color1)
        self.style.configure("TRadiobutton", background=color1)
        self.export_var=tk.IntVar()
        # 如果有特定的控件需要调整，比如文本框的前景色等，也可以设置
        self.style.configure("TButton", foreground="black",font=("Lato", 11, "bold"))
        self.style.configure("TLabel", foreground="black",font=("Lato", 10, "bold"))
        # 初始化步骤
        self.step = 0  # 0: Load Data, 1: Select Range, 2: Peak Finding

        # 创建顶部导航按钮
        self.nav_frame = ttk.Frame(root)
        self.nav_frame.pack(fill=tk.X, pady=5)
        self.prev_button = ttk.Button(self.nav_frame, text="←", command=self.prev_step, width=10)
        self.prev_button.pack(side=tk.LEFT, padx=10)
        self.next_button = ttk.Button(self.nav_frame, text="→", command=self.next_step, width=10)
        self.next_button.pack(side=tk.RIGHT, padx=10)

        # 初始化参数
        self.add_peak_slot1 = tk.StringVar(value="0.02")
        self.peakslot1 = tk.StringVar(value="0.01")
        self.add_peak_slot = float(self.add_peak_slot1.get())
        self.peakslot = float(self.peakslot1.get())

        # 初始化图形和轴
        self.fig = None
        self.ax = None
        self.invert = [self.invert0, self.invert1, self.invert2, self.invert3, self.invert4]

        # 创建主要内容框架

        self.content_frame = ttk.Frame(root)
        self.content_frame.pack(fill=tk.BOTH, expand=True)

        # 初始化数据存储
        self.file_path = None
        self.raw_data = None
        self.df = None
        self.x = None
        self.y = None
        self.filtered_x = None
        self.filtered_y = None
        self.peaks_x = []
        self.peaks_y = []
        self.center_var = None
        self.slot_var = None
        self.selector = None
        self.peaks = [[], [], [], [], []]
        self.powers = [[], [], [], [], []]
        self.peaks_index = [[], [], [], [], []]
        self.orders = [[], [], [], [], []]
        self.PEAKs = [0] * 5
        self.FSRs = [0] * 5
        self.exports = [self.export] * 5
        self.fsrs = [0] * 5
        self.plot = [1] * 5
        self.renew = [0] * 5
        self.peaknum = 0
        self.file_name0 = tk.StringVar()

        # 初始化界面
        self.update_ui()
        self.FSR_container = ttk.Frame(self.content_frame)
        self.peaks_container = ttk.Frame(self.content_frame)

    def renew_para(self):
        """更新参数"""
        self.add_peak_slot = float(self.add_peak_slot1.get())
        self.peakslot = float(self.peakslot1.get())
        self.peak_depth_var=float(self.peak_depth.get())

    def clear_frame(self):
        """清除当前界面组件"""
        for widget in self.content_frame.winfo_children():
            widget.destroy()

    def update_ui(self):
        """根据步骤更新界面"""
        self.clear_frame()
        if self.step == 0:
            self.load_data_ui()
        elif self.step == 1:
            self.select_range_ui()
        elif self.step == 2.5:
            self.find_peaks_ui()
        elif self.step == 3:
            self.analyze_peaks_ui()
        elif self.step==2:
            self.find_peaks_ui2()


    def load_data_ui(self):
        """加载数据界面"""
        title_label = ttk.Label(self.content_frame, text="Step 1: Load Data", font=("Arial", 16, "bold"))
        title_label.pack(pady=10)

        load_button = ttk.Button(self.content_frame, text="Load Data", command=self.load_data)
        load_button.pack(pady=10)

        self.preview_text = tk.Text(self.content_frame, height=20, width=100, font=("Arial", 10))
        self.preview_text.pack(pady=10)

        confirm_button = ttk.Button(self.content_frame, text="Confirm Selection", command=self.process_data)
        confirm_button.pack(pady=10)

    def select_range_ui(self):
        """选择范围界面"""
        title_label = ttk.Label(self.content_frame, text="Step 2: Select Range", font=("Arial", 16, "bold"))
        title_label.pack(pady=10)

        # 数据选择模式
        self.mode_var = tk.StringVar(value="Overview")
        mode_frame = ttk.Frame(self.content_frame)
        mode_frame.pack(pady=10)

        ttk.Radiobutton(mode_frame, text="Show overview", variable=self.mode_var, value="Overview",
                        command=self.update_input_fields).grid(row=0, column=0, sticky=tk.W)
        ttk.Radiobutton(mode_frame, text="Span (Center & Width)", variable=self.mode_var, value="Span",
                        command=self.update_input_fields).grid(row=1, column=0, sticky=tk.W)
        ttk.Radiobutton(mode_frame, text="Ini & End", variable=self.mode_var, value="IniEnd",
                        command=self.update_input_fields).grid(row=2, column=0, sticky=tk.W)

        self.input_frame = ttk.Frame(self.content_frame)
        self.input_frame.pack(fill=tk.X, pady=10)
        self.update_input_fields()

        confirm_button = ttk.Button(self.content_frame, text="Confirm Selection", command=self.apply_range)
        confirm_button.pack(pady=10)

        self.show_overview()

    def export_preparation(self):
        self.export=int(self.export_var.get())
        self.exports = [self.export, self.export, self.export, self.export, self.export]
        if self.export == 1:
            headers = ['wavelength(nm)', 'r2', 'Q(M)', 'Qe(M)', 'Qi(M)', 'kappa(MHz)', 'kappa_e(MHz)', 'kappa_i(MHz)',
                       'lw(pm)', 'lw_e(pm)', 'lw_i(pm)']

            # 确保在这里获取到的值是最新的
            file_name = self.file_name0.get()
            print(f"File name: {file_name}")  # 打印出文件名以确认它是否正确更新

            # 创建输出文件名
            self.output_name = os.path.join(self.save_folder_path, f"{file_name}_categorized_peaks.csv")

            # 将处理结果保存为 CSV 文件
            with open(self.output_name, 'w', encoding='utf8', newline='') as f:
                writer = csv.writer(f)
                writer.writerow([file_name])  # 写入文件名作为第一行
                writer.writerow(headers)  # 写入其他数据表头

    def turn_to_height_mode(self):
        self.step-=0.5
        self.update_ui()
    def turn_to_multi_mode(self):
        self.step+=0.5
        print(self.step)
        self.update_ui()
    def find_peaks_ui2(self):
        """寻峰界面"""
        self.FSRs=[0]
        # 标题
        # 创建 peaks_frame，并确保它在 "+" 按钮的下方
        ttk.Label(self.content_frame, text="Step 3: Find Peaks", font=("Arial", 16, "bold")).pack(pady=10)
        ttk.Button(self.content_frame, text="Select Multimode Peaks",command=self.turn_to_multi_mode).pack(pady=10)
        # 让文本框占据上方一行
        self.content_frame1 = ttk.Frame(self.content_frame)
        self.content_frame1.pack(pady=5)
        ttk.Label(self.content_frame1, text="Adding tolerance").grid(row=0, column=0, padx=5, pady=5)
        ttk.Entry(self.content_frame1, textvariable=self.add_peak_slot1, width=5).grid(row=0, column=1, padx=5, pady=5)
        ttk.Label(self.content_frame1, text="Extending tolerance").grid(row=0, column=2, padx=5, pady=5)
        ttk.Entry(self.content_frame1, textvariable=self.peakslot1, width=5).grid(row=0, column=3, padx=5, pady=5)
        ttk.Button(self.content_frame1, text="Set", width=5, command=self.renew_para).grid(row=0, column=4, padx=5,
                                                                                           pady=10, columnspan=1)
        ttk.Label(self.content_frame1, text="The selecting height").grid(row=0, column=5, padx=5, pady=5)
        ttk.Entry(self.content_frame1, textvariable=self.peak_depth,width=5).grid(row=0, column=6, padx=5, pady=5)
        ###ttk.Label(self.content_frame1, text="Extending tolerance").grid(row=0, column=2, padx=5, pady=5)
        ###ttk.Entry(self.content_frame1, textvariable=self.peakslot1,width=5).grid(row=0, column=3, padx=5, pady=5)
        ttk.Button(self.content_frame1, text="Set", width=5,command=self.height_set).grid(row=0, column=7, padx=5, pady=10,columnspan=1)
        self.FSR_container = ttk.Frame(self.content_frame)
        self.FSR_container.pack(pady=5)
        for i in range(1):
            self.fsrs[i]=0
            self.FSRs[i] = ttk.Label(self.FSR_container, text=f"FSR={self.fsrs[i]}nm", width=10, anchor="e")
            self.FSRs[i].grid(row=0, column=0, columnspan=4, padx=5)
            ttk.Button(self.FSR_container, text="Hide", command=self.invert[i],width=5).grid(row=0, column=4, padx=5)
            ttk.Button(self.FSR_container, text="Clear", command=lambda index=i: self.destroy_peaks(index),width=5).grid(row=0,
                                                                                                                 column=5,
                                                                                                                 padx=5)
        self.peaks_container = ttk.Frame(self.content_frame)
        self.peaks_container.pack(pady=20)  # 让文本框占据上方一行

        # 创建 5 个文本框，并放入 peaks_container 中
        self.PEAKs = [tk.Text(self.peaks_container,width=20,height=8) for I in range(1)]
        for i, kind in enumerate(self.PEAKs):
            kind.pack(side=tk.LEFT,padx=45)  # 水平排列
            for j in self.peaks[i]:
                self.peaks[i]=[]
                kind.insert(tk.END, j)
                kind.insert(tk.END, "\n")

        self.renews_container = ttk.Frame(self.content_frame)
        self.renews_container.pack(pady=1)  # 让文本框占据上方一行

        # 创建 5 个文本框，并放入 peaks_container 中
        self.renews = [ttk.Button(self.renews_container, width=20) for I in range(1)]
        for i, kind in enumerate(self.renews):
            kind.pack(side=tk.LEFT,padx=20)
            kind['text'] = "remove certain peaks"
            kind['command'] = lambda index=i: self.renew_for_one(index)
        self.adds_container = ttk.Frame(self.content_frame)
        self.adds_container.pack(pady=1)  # 让文本框占据上方一行

        # 创建 5 个文本框，并放入 peaks_container 中
        self.adds = [ttk.Button(self.adds_container, width=20) for I in range(1)]
        for i, kind in enumerate(self.adds):
            kind.pack(side=tk.LEFT,padx=20)
            kind['text'] = "add more peaks"
            kind['command'] = lambda index=i: self.add_single_peak(index)

            # 水平排列
        # "+" 按钮，放在文本框的下方


        # 绘图
        self.fig, self.ax = plt.subplots(figsize=(8, 6))  # 增大图形的尺寸
        self.canvas = FigureCanvasTkAgg(self.fig, master=self.content_frame)
        self.canvas_widget = self.canvas.get_tk_widget()
        self.canvas_widget.pack(fill=tk.BOTH, expand=True)
        self.plot_data(self.filtered_x, self.filtered_y)
    def height_set(self):
        self.renew_para()
        self.peak_in_x = self.filtered_x
        self.peak_in_y = self.filtered_y
        peaks1, _ = find_peaks(-self.peak_in_y, height=-self.peak_depth_var, threshold=0, distance=float(self.peak_distance.get()), prominence=.005,
                               width=None,
                               wlen=None, rel_height=0.5, plateau_size=None)
        peak_index = peaks1
        peaks=self.filtered_x[peaks1]
        powers=self.filtered_y[peaks1]
        i=0


        if len(peaks1) > 1:
            approximate_fsr=min([abs(peaks[i]-peaks[i+1]) for i in range(len(peaks)-1)])
            orders=[round((peaks[i]-peaks[0])/approximate_fsr,0) for i in range(len(peaks))]
        # 在图中标记第一个峰

        self.orders[i]=orders
        self.peaks_index[i]=peak_index
        self.peaks[i]=peaks
        self.powers[i]=powers
        self.update_peaks_info()
        self.plot_peaks()

    def find_peaks_ui(self):
        """寻峰界面"""
        # 标题
        self.FSRs = [0] * 5
        #self.fsrs = [0] * 5
        # 创建 peaks_frame，并确保它在 "+" 按钮的下方
        ttk.Label(self.content_frame, text="Step 3: Find Peaks", font=("Arial", 16, "bold")).pack(pady=10)
        ttk.Button(self.content_frame, text="Select Peaks with depth",command=self.turn_to_height_mode).pack(pady=10)
        # 让文本框占据上方一行
        self.content_frame1 = ttk.Frame(self.content_frame)
        self.content_frame1.pack(pady=5)
        self.peaks = [[], [], [], [], []]
        self.powers = [[], [], [], [], []]
        self.peaks_index = [[], [], [], [], []]
        self.orders = [[], [], [], [], []]

        ttk.Label(self.content_frame1, text="Adding tolerance").grid(row=0, column=0, padx=5, pady=5)
        ttk.Entry(self.content_frame1, textvariable=self.add_peak_slot1,width=5).grid(row=0, column=1, padx=5, pady=5)
        ttk.Label(self.content_frame1, text="Extending tolerance").grid(row=0, column=2, padx=5, pady=5)
        ttk.Entry(self.content_frame1, textvariable=self.peakslot1,width=5).grid(row=0, column=3, padx=5, pady=5)
        ttk.Button(self.content_frame1, text="Set", width=5,command=self.renew_para).grid(row=0, column=4, padx=5, pady=10,columnspan=3)
        self.FSR_container = ttk.Frame(self.content_frame)
        self.FSR_container.pack(pady=5)
        for i in range(5):
            self.FSRs[i]=ttk.Label(self.FSR_container, text=f"FSR={self.fsrs[i]}nm", width=10,anchor="e")
            self.FSRs[i].grid(row=0, column=4*i, columnspan=2,padx=5)
            ttk.Button(self.FSR_container, text="Hide", command=self.invert[i],width=5).grid(row=0, column=4*i+2, padx=5)
            ttk.Button(self.FSR_container, text="Clear", command=lambda index=i: self.destroy_peaks(index),width=5).grid(row=0,
                                                                                                                 column=4*i+3,
                                                                                                                 padx=5)
        self.peaks_container = ttk.Frame(self.content_frame)
        self.peaks_container.pack(pady=20)  # 让文本框占据上方一行

        # 创建 5 个文本框，并放入 peaks_container 中
        self.PEAKs = [tk.Text(self.peaks_container,width=20,height=8) for I in range(5)]
        for i, kind in enumerate(self.PEAKs):
            kind.pack(side=tk.LEFT,padx=45)  # 水平排列
            for j in self.peaks[i]:
                kind.insert(tk.END, j)
                kind.insert(tk.END, "\n")

        self.renews_container = ttk.Frame(self.content_frame)
        self.renews_container.pack(pady=1)  # 让文本框占据上方一行

        # 创建 5 个文本框，并放入 peaks_container 中
        self.renews = [ttk.Button(self.renews_container, width=20) for I in range(5)]
        for i, kind in enumerate(self.renews):
            kind.pack(side=tk.LEFT,padx=20)
            kind['text'] = "remove certain peaks"
            kind['command'] = lambda index=i: self.renew_for_one(index)
        self.extends_container = ttk.Frame(self.content_frame)
        self.extends_container.pack(pady=1)  # 让文本框占据上方一行

        # 创建 5 个文本框，并放入 peaks_container 中
        self.extends = [ttk.Button(self.extends_container, width=20) for I in range(5)]
        for i, kind in enumerate(self.extends):
            kind.pack(side=tk.LEFT,padx=20)
            kind['text'] = "extend to more peaks"
            kind['command'] = lambda index=i: self.extend(index)
        self.adds_container = ttk.Frame(self.content_frame)
        self.adds_container.pack(pady=1)  # 让文本框占据上方一行

        # 创建 5 个文本框，并放入 peaks_container 中
        self.adds = [ttk.Button(self.adds_container, width=20) for I in range(5)]
        for i, kind in enumerate(self.adds):
            kind.pack(side=tk.LEFT,padx=20)
            kind['text'] = "add more peaks"
            kind['command'] = lambda index=i: self.add_single_peak(index)

            # 水平排列
        # "+" 按钮，放在文本框的下方
        tk.Button(self.content_frame, text="+", command=self.add_peak).pack(pady=10)  # 确保 peaks_frame 位于下方
        self.update_peaks_info()
        # 绘图
        self.fig, self.ax = plt.subplots(figsize=(8, 6))  # 增大图形的尺寸
        self.canvas = FigureCanvasTkAgg(self.fig, master=self.content_frame)
        self.canvas_widget = self.canvas.get_tk_widget()
        self.canvas_widget.pack(fill=tk.BOTH, expand=True)
        self.plot_data(self.filtered_x, self.filtered_y)
        # 显示当前峰列表
    def process_data(self):
        """处理数据"""
        if self.file_path.endswith(".csv"):
            self.df = pd.read_csv(self.file_path, skiprows=self.skip_rows)
        else:
            self.df = pd.read_csv(self.file_path, sep='\s+', header=None, skiprows=self.skip_rows)

        self.x = self.df.iloc[:, 0].values
        self.y = self.df.iloc[:, 1].values
        messagebox.showinfo("Info", "Data processed! Move to the next step.")

    def load_data(self):
        """加载 CSV 或 DAT 文件"""
        self.file_path = filedialog.askopenfilename(
            filetypes=[("CSV files", "*.csv"), ("DAT files", "*.dat"), ("All Files", "*.*")])
        if not self.file_path:
            return

        with open(self.file_path, "r", encoding="utf-8") as file:
            lines = file.readlines()

        preview_text = "".join(lines[:100])
        self.preview_text.delete("1.0", tk.END)
        self.preview_text.insert(tk.END, preview_text)

        self.raw_data = lines
        # messagebox.showinfo("Info", "File loaded! Detecting data start...")

        self.auto_detect_start()

    def auto_detect_start(self):
        """自动检测数据起始行"""
        for i, line in enumerate(self.raw_data):
            parts = line.strip().split()
            if len(parts) >= 2:
                try:
                    float(parts[0])
                    float(parts[1])
                    self.skip_rows = i
                    # messagebox.showinfo("Detected", f"Data starts at line {i}")
                    return
                except ValueError:
                    continue
        self.skip_rows = 0




    def select_save_folder(self):
        """让用户选择保存文件的根文件夹"""
        folder_selected = tkinter.filedialog.askdirectory(title="Select Folder to Save Files")
        if folder_selected:  # 确保用户选择了文件夹
            self.save_folder_path = folder_selected
            print(f"Save folder set to: {self.save_folder_path}")
        else:
            if self.export == 1:
                print("No folder selected. Please try again.")

    def analyze_peaks_ui(self):
        """分析峰界面"""
        title_label = ttk.Label(self.content_frame, text="Step 4: Analyze Peaks", font=("Arial", 16, "bold"))
        title_label.pack(pady=10)
        self.rl=ttk.Frame(self.content_frame)
        self.rl.pack(pady=10)
        tk.Label(self.rl, text="resonance region(nm)", width=20).grid(row=0, column=0, pady=10)
        tk.Entry(self.rl, textvariable=self.resonance_lw_var, width=20).grid(row=0,column=1,pady=10)
         # 用于存储每个 FSR 的拟合结
        self.ex=ttk.Frame(self.content_frame)
        self.ex.pack(pady=10)
        export_check = ttk.Checkbutton(self.ex, text="Export?", variable=self.export_var)
        export_check.grid(row=0, column=0,pady=10)

        # 让用户选择保存的根目录
        self.select_folder_button = ttk.Button(self.ex, text="Select Save Folder",
                                               command=self.select_save_folder)
        self.select_folder_button.grid(row=0, column=1,pady=10)

        input_filename = ttk.Label(self.ex, text="The file name you'd like to save as",
                                   font=("Arial", 12))
        input_filename.grid(row=0, column=2,pady=10)
        Filename = ttk.Entry(self.ex, textvariable=self.file_name0, width=50)
        Filename.grid(row=0, column=3,pady=10)
        Confirm=ttk.Button(self.ex, text="Confirm Selection", command=self.export_preparation)
        Confirm.grid(row=0, column=4,pady=10)
        self.cl=ttk.Frame(self.content_frame)
        self.cl.pack(pady=10)
        tk.Label(self.cl, text="Click to analyze certain-mode peaks").pack(side=tk.LEFT)
        for i in range(5):
            if self.fsrs[i] > 0:
                ttk.Button(self.cl, text=f"FSR={self.fsrs[i]}nm", command=lambda index=i: self.fit_Q(index)).pack(side=tk.LEFT)
        self.content_frame2=ttk.Frame(self.content_frame,width=1500)
        self.content_frame2.pack(fill=tk.BOTH, expand=True)
    def fit_Q(self, j):
        for widget in self.content_frame2.winfo_children():
            widget.destroy()
        self.fit_Q_data_frame = tk.Frame(self.content_frame2)
        self.fit_Q_data_frame.pack(fill=tk.X)
        #if self.canvas:
            #self.canvas.delete("all")
        # 创建 Canvas 和 Scrollbar
        self.canvas = tk.Canvas(self.fit_Q_data_frame, height=1000, width=80)
        self.scrollbar = tk.Scrollbar(self.fit_Q_data_frame, orient="vertical", command=self.canvas.yview)
        self.scrollable_frame = tk.Frame(self.canvas)
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: self.canvas.configure(
                scrollregion=self.canvas.bbox("all")
            )
        )
        self.canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.scrollbar.pack(side="right", fill="y")
        a = 0
        self.resonance_lw = float(self.resonance_lw_var.get())
        for m in range(1):
            if self.exports[j] == 1:
                with open(self.output_name, mode='a', newline='', encoding='utf8') as cfa:
                    wf = csv.writer(cfa)
                    wf.writerow([f'Categorizing FSR={round(self.fsrs[j], 3)}nm'])

            peaks = self.peaks_index[j]
            l = len(peaks)
            for i in peaks:
                a += 1
                print('resonance wavelength: ', self.filtered_x[i])
                resonance_index = np.where(
                    (self.filtered_x > self.filtered_x[i] - self.resonance_lw / 2)
                    & (self.filtered_x < self.filtered_x[i] + self.resonance_lw / 2))
                resonance_1_x = self.filtered_x[resonance_index]
                resonance_1_y = self.filtered_y[resonance_index]
                p0 = [.1, 0.5, 0.1, self.filtered_x[i]]
                popt, pcov = optimize.curve_fit(target_fun, resonance_1_x, resonance_1_y,
                                                p0=p0, bounds=(0, np.inf), maxfev=5000)
                y_fit = np.array([target_fun(ii, *popt) for ii in resonance_1_x])
                r2 = r2_score(resonance_1_y, target_fun(resonance_1_x, *popt))

                lw_e = popt[1]
                lw_i = popt[2]
                wl_center = popt[3]
                kappa_e = delta_wl_to_f(lw_e, wl_center)
                kappa_i = delta_wl_to_f(lw_i, wl_center)
                lw = lw_e + lw_i
                kappa = kappa_e + kappa_i
                Q = wl_center / lw
                Q_e = wl_center / lw_e
                Q_i = wl_center / lw_i
                resonance_para_tmp = np.array([Q, kappa, kappa_e, kappa_i, lw, lw_e, lw_i])
                to_write = f'lw:{round(lw * 10 ** 3, 2)}pm, {round(kappa, 4)} GHz\n,r2: {round(r2, 4)}\n Q:{round(Q * 10 ** -6, 4)}million\nkappa_e = {round(kappa_e * 10 ** 3, 0)} MHz,kappa_i = {round(kappa_i * 10 ** 3, 0)} MHz'

                # 为每个 FSR 创建一个文件夹
                folder_name = os.path.join(self.save_folder_path, f"{self.file_name0.get()}_FSR={self.fsrs[j]}nm")
                if not os.path.exists(folder_name):
                    os.makedirs(folder_name)

                # 保存图像
                self.image_name = f'{self.filtered_x[i]}nm, r2={r2}.png'
                self.new_image_path = os.path.join(folder_name, self.image_name)
                self.create_plot(j, resonance_1_x, resonance_1_y, y_fit,
                                 f"FSR={round(self.fsrs[j], 3)}nm, wl={self.filtered_x[i]}nm", to_write)

                # 导出 CSV 数据
                if self.exports[j] == 1:
                    with open(self.output_name, mode='a', newline='', encoding='utf8') as cfa:
                        wf = csv.writer(cfa)
                        wf.writerow(
                            [self.filtered_x[i], r2, round(Q * 10 ** -6, 4), round(Q_e * 10 ** -6, 4),
                             round(Q_i * 10 ** -6, 4),
                             round(kappa * 10 ** 3, 0), round(kappa_e * 10 ** 3, 0), round(kappa_i * 10 ** 3, 0),
                             round(lw * 10 ** 3, 2), round(lw_e * 10 ** 3, 2), round(lw_i * 10 ** 3, 2)])

        # 缓存结果
        self.exports[j] = 0

    def create_plot(self, plot_number, data_x, data_y, fit_y, title, annotation_text):
        # 创建一个子框架
        plot_frame = tk.Frame(self.scrollable_frame)
        plot_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True, pady=10)

        # 创建一个 Matplotlib 图表
        fig, ax = plt.subplots(figsize=(16, 6))
        ax.plot(data_x, data_y, label='Data')
        ax.plot(data_x, fit_y, label='Fit')
        ax.set_title(title)

        ax.set_xlim(data_x.min(), 1.4 * data_x.max() - 0.4*data_x.min())

        # 调整子图布局，确保右侧有足够空间
        #plt.subplots_adjust(left=1)

        # 添加文字注解
        # 确保注释的位置在图表的正右边
        x_annotation = (max(data_x) - min(data_x)) * (-0.1) + max(data_x)  # 注释的 x 位置为数据最大值的 1.1 倍，确保在图表右侧
        y_annotation = (max(data_y)+min(data_y)) * 0.5  # 注释的 y 位置为数据最大值的 0.5 倍，确保在图表中心
        ax.annotate(annotation_text, xy=(x_annotation, y_annotation), xytext=(x_annotation, y_annotation),
                    arrowprops=dict(facecolor='black', shrink=0.05), ha='left', va='center')
        ax.legend()
        # 将图表嵌入到 Tkinter 窗口中
        canvas = FigureCanvasTkAgg(fig, master=plot_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        if self.exports[plot_number] == 1:
            plt.savefig(self.new_image_path, dpi=700, bbox_inches='tight')

    def update_input_fields(self):
        """根据模式更新输入框"""
        for widget in self.input_frame.winfo_children():
            widget.destroy()
        if self.mode_var.get() == "Span":
            # Span模式：中心值和宽度
            tk.Label(self.input_frame, text="Center Value").pack(side=tk.LEFT)
            self.center_var = tk.DoubleVar(value=1550)
            tk.Entry(self.input_frame, textvariable=self.center_var).pack(side=tk.LEFT)

            tk.Label(self.input_frame, text="Width").pack(side=tk.LEFT)
            self.slot_var = tk.DoubleVar(value=20)
            tk.Entry(self.input_frame, textvariable=self.slot_var).pack(side=tk.LEFT)
        elif self.mode_var.get() == "Overview":
            pass
        else:
            # Ini & End模式：起始值和终止值
            tk.Label(self.input_frame, text="Start Value").pack(side=tk.LEFT)
            self.start_var = tk.DoubleVar(value=1540)
            tk.Entry(self.input_frame, textvariable=self.start_var).pack(side=tk.LEFT)

            tk.Label(self.input_frame, text="End Value").pack(side=tk.LEFT)
            self.end_var = tk.DoubleVar(value=1560)
            tk.Entry(self.input_frame, textvariable=self.end_var).pack(side=tk.LEFT)

    def show_overview(self):
        if self.ax:
            self.ax.clear()
        else:
            self.fig, self.ax = plt.subplots(figsize=(8, 6))  # 增大图形的尺寸
            self.canvas = FigureCanvasTkAgg(self.fig, master=self.content_frame)
            self.canvas_widget = self.canvas.get_tk_widget()
            self.canvas_widget.pack(fill=tk.BOTH, expand=True)

        # 初始化绘图
        self.plot_data(self.x, self.y)
        self.apply_range()

    def apply_range(self):
        """应用选择的数据范围并更新图表"""
        if self.x is None or self.y is None:
            messagebox.showerror("Error", "Please load and process data first!")
            return

        if self.mode_var.get() == "Span":
            center = self.center_var.get()
            width = self.slot_var.get()
            self.filtered_x = self.x[(self.x > center - width / 2) & (self.x < center + width / 2)]
            self.filtered_y = self.y[(self.x > center - width / 2) & (self.x < center + width / 2)]
        elif self.mode_var.get() == "Overview":
            self.filtered_x = self.x
            self.filtered_y = self.y
        else:
            start = self.start_var.get()
            end = self.end_var.get()
            self.filtered_x = self.x[(self.x >= start) & (self.x <= end)]
            self.filtered_y = self.y[(self.x >= start) & (self.x <= end)]

        # 绘图
        self.plot_data(self.filtered_x, self.filtered_y)
        messagebox.showinfo("Info", "Data range applied!")

    def plot_data(self, data_x, data_y):
        """绘制数据"""
        self.ax.clear()  # 清除之前的图形
        # 绘制筛选后的数据
        if data_x is not None and data_y is not None:
            self.ax.plot(data_x, data_y, color='purple', label="Filtered Data")  # 用紫色线绘制筛选后的数据

        self.ax.legend()
        #self.ax.set_title("Data Selection")
        self.ax.set_xlabel("X")
        self.ax.set_ylabel("Y")
        self.canvas.draw()

    def on_select(self, eclick, erelease):
        """处理选择区域"""
        x_min, x_max = sorted([eclick.xdata, erelease.xdata])
        y_min, y_max = sorted([eclick.ydata, erelease.ydata])

        self.filtered_x = self.x[(self.x >= x_min) & (self.x <= x_max)]
        self.filtered_y = self.y[(self.x >= x_min) & (self.x <= x_max)]

        self.plot_data(self.filtered_x, self.filtered_y)

    def plot_peaks(self):
        """绘制标记的峰"""
        self.ax.clear()  # 清除图形
        self.ax.set_ylim((0,self.filtered_y.max()))
        self.plot_data(self.filtered_x, self.filtered_y)
        color = ['red', 'green', 'blue', 'cyan', 'magenta', 'yellow']
        # 绘制剩余的标记峰
        for i in range(5):
            if self.plot[i] and self.fsrs[i]:
                print(self.peaks[i], self.orders[i])

                self.ax.plot(self.peaks[i], self.powers[i], 'rx', color=color[i], label=f"FSR={self.fsrs[i]}")

        self.ax.legend()
        self.canvas.draw()


    def add_single_peak(self, i):
        self.renew_para()
        self.moreadd = 1
        self.fig.canvas.mpl_connect('button_press_event',
                                    lambda event, index=i: self.on_click_add_single_peak(event, index))

    def add_peak(self):
        self.renew_para()
        """开始添加峰"""
        self.peak_click_stage = 1  # 设置为第一阶段
        messagebox.showinfo("Info", "Add the first example points (click on the plot)")
        self.fig.canvas.mpl_connect('button_press_event', self.on_click_add_peak)

    def on_click_add_peak(self, event):
        """根据点击顺序添加峰"""
        if self.peak_click_stage == 1:
            # messagebox.showinfo("Info", "Add the first example points (click on the plot)")
            self.peak_in_x = self.filtered_x[(self.filtered_x > event.xdata - self.add_peak_slot / 2) & (
                        self.filtered_x < event.xdata + self.add_peak_slot / 2)]
            self.peak_in_y = self.filtered_y[(self.filtered_x > event.xdata - self.add_peak_slot / 2) & (
                    self.filtered_x < event.xdata + self.add_peak_slot / 2)]
            peaks1, _ = find_peaks(-self.peak_in_y, height=-(event.y + 0.1), threshold=0, distance=500, prominence=.005,
                                   width=None,
                                   wlen=None, rel_height=0.5, plateau_size=None)
            index=self.peak_in_y[peaks1].argmin()
            peak_index = peaks1[index] + self.filtered_x.tolist().index(self.peak_in_x[0])
            self.peaks_x = []
            self.peaks_y = []
            self.peaks_index[self.peaknum] = []
            self.orders[self.peaknum] = []
            # 在图中标记第一个峰
            self.peaks_index[self.peaknum].append(peak_index)
            self.peaks_x.append(self.peak_in_x[peaks1[index]])
            self.peaks_y.append(self.peak_in_y[peaks1[index]])
            self.plot_peaks()
            self.orders[self.peaknum].append(0)
            self.peak_click_stage = 2  # 进入第二阶段
            messagebox.showinfo("Info", "Add the Second example points (click on the plot)")
        elif self.peak_click_stage == 2:
            self.peak_in_x = self.filtered_x[
                (self.filtered_x > event.xdata - self.peakslot / 2) & (
                            self.filtered_x < event.xdata + self.peakslot / 2)]
            self.peak_in_y = self.filtered_y[
                (self.filtered_x > event.xdata - self.peakslot / 2) & (
                            self.filtered_x < event.xdata + self.peakslot / 2)]
            peaks1, _ = find_peaks(-self.peak_in_y, height=-(event.y + 0.05), threshold=0, distance=500,
                                   prominence=.005, width=None,
                                   wlen=None, rel_height=0.5, plateau_size=None)
            index = self.peak_in_y[peaks1].argmin()
            peak_index = peaks1[index] + self.filtered_x.tolist().index(self.peak_in_x[0])
            self.peaks_index[self.peaknum].append(peak_index)
            # 在图中标记第一个峰
            self.peaks_x.append(self.peak_in_x[peaks1[index]])
            self.peaks_y.append(self.peak_in_y[peaks1[index]])
            self.peaks[self.peaknum] = (self.peaks_x)
            self.powers[self.peaknum] = (self.peaks_y)
            # 计算 FSR
            fsr = abs(self.peaks_x[1] - self.peaks_x[0])
            self.fsrs[self.peaknum] = round(fsr, 3)
            self.orders[self.peaknum].append(1)
            self.plot_peaks()
            self.peaknum += 1
            self.peak_click_stage = 0
            self.update_peaks_info()

    def on_click_add_single_peak(self, event, i):
        """根据点击顺序添加峰"""
        if self.moreadd == 1:
            # messagebox.showinfo("Info", "Add the first example points (click on the plot)")
            self.peak_in_x = self.filtered_x[(self.filtered_x > event.xdata - self.add_peak_slot / 2) & (
                        self.filtered_x < event.xdata + self.add_peak_slot / 2)]
            self.peak_in_y = self.filtered_y[(self.filtered_x > event.xdata - self.add_peak_slot / 2) & (
                    self.filtered_x < event.xdata + self.add_peak_slot / 2)]
            peaks1, _ = find_peaks(-self.peak_in_y, height=-(event.y + 0.1), threshold=0, distance=500, prominence=.005,
                                   width=None,
                                   wlen=None, rel_height=0.5, plateau_size=None)
            index = self.peak_in_y[peaks1].argmin()
            peak_index = peaks1[index] + self.filtered_x.tolist().index(self.peak_in_x[0])
            # 在图中标记第一个峰
            add = 1

            if len(self.peaks[i]) == 0:
                order = 0
            elif len(self.peaks[i]) == 1:
                if self.peak_in_x[0] > self.peaks[i][0]:
                    order = 1
                elif self.peak_in_x[0] < self.peaks[i][0]:
                    order = 0
                    self.orders[i] = [1]
                else:
                    messagebox.showinfo("Info", "Illegal Region to add peak!")
                    add = 0
            else:
                order = int(
                    round((self.peak_in_x[peaks1[index]] - self.peaks[i][0]) / self.fsrs[i], 1))+self.orders[i][0]
                if order == 0:
                    messagebox.showinfo("Info", "Illegal Region to add peak!")
                    add = 0
                else:
                    if order in self.orders[i]:
                        messagebox.showinfo("Info", "Illegal Region to add peak!")
                        add = 0
            if add == 1:
                self.peaks_index[i].append(peak_index)
                self.peaks[i].append(self.peak_in_x[peaks1[index]])
                self.powers[i].append(self.peak_in_y[peaks1[index]])
                peaks = self.peaks[i]
                if len(peaks) > 1:
                    if self.fsrs[i] > 0:
                        approximate_fsr = self.fsrs[i]
                    else:
                        approximate_fsr = min([abs(peaks[i] - peaks[i + 1]) for i in range(len(peaks) - 1)])
                    orders = [round((peaks[i] - peaks[0]) / approximate_fsr, 0) for i in range(len(peaks))]
                    self.orders[i] = orders
                self.update_peaks_info()
                self.plot_peaks()
        self.moreadd = 0

    def update_peaks_info(self):
        for i, kind in enumerate(self.PEAKs):
            kind.delete("1.0", tk.END)
            # 假设这是你的两个列表
            if len(self.peaks[i]) > 1:
                list1 = self.peaks[i]
                list2 = self.powers[i]
                list3 = self.peaks_index[i]
                list4 = self.orders[i]
                # 使用 zip 将两个列表组合在一起
                combined = list(zip(list1, list2, list3, list4))
                # 按照第一个列表的元素从小到大排序
                sorted_combined = sorted(combined, key=lambda x: x[0])
                # 将排序后的列表分开
                sorted_list1, sorted_list2, sorted_list3, sorted_list4 = zip(*sorted_combined)
                # 转换回列表（如果需要）
                self.peaks[i] = list(sorted_list1)
                self.powers[i] = list(sorted_list2)
                self.peaks_index[i] = list(sorted_list3)
                self.orders[i] = list(sorted_list4)
                coeffs = np.polyfit(self.orders[i], self.peaks[i], 1)
                # coeffs[0] 是斜率 m，coeffs[1] 是截距 b
                m, b = coeffs
                self.fsrs[i] = m
            for j in self.peaks[i]:
                kind.insert(tk.END, j)
                kind.insert(tk.END, "\n")
        for i, kind in enumerate(self.FSRs):
            kind['text'] = f"FSR={round(self.fsrs[i], 3)}nm"  # 水平排列

    def destroy_peaks(self, i):
        for j in range(i, 4):
            if self.fsrs[j] > 0:
                self.peaks[j] = self.peaks[j + 1]
                self.powers[j] = self.powers[j + 1]
                self.peaks_index[j] = self.peaks_index[j + 1]
                self.orders[j] = self.orders[j + 1]
                self.fsrs[j] = self.fsrs[j + 1]
                self.plot[j] = self.plot[j + 1]
                self.renew[j] = self.renew[j + 1]
            else:
                self.peaks[j] = []
                self.powers[j] = []
                self.peaks_index[j] = []
                self.orders[j] = []
                self.fsrs[j] = 0
                self.plot[j] = 1
                self.renew[j] = 0

        self.peaknum -= 1
        self.update_peaks_info()
        self.plot_peaks()

    def extend(self, i):
        if len(self.peaks[i]) > 1:
            approximate_fsr = self.fsrs[i]
            peakslot = self.peakslot
            x0 = self.peaks[i][-1] + approximate_fsr
            certain_peaks = list(self.peaks_index[i])
            order = 1
            while x0 + peakslot / 2 < self.filtered_x[-1]:
                try_index = np.where((self.filtered_x > x0 - peakslot / 2) & (self.filtered_x < x0 + peakslot / 2))
                try_end = try_index[-1][0]
                tryslot_x = self.filtered_x[try_index]
                tryslot_y = self.filtered_y[try_index]
                if np.max(tryslot_y) - np.min(tryslot_y) > 0.01:
                    try_limit = np.min(tryslot_y)
                else:
                    try_limit = -1
                peakstry, _ = find_peaks(-tryslot_y, height=-try_limit, threshold=0, distance=500, prominence=.005,
                                         width=None, wlen=None, rel_height=0.5, plateau_size=None)
                if not peakstry:
                    x0 += approximate_fsr
                    order += 1
                else:
                    formerx0 = float(x0 - approximate_fsr)
                    x0_index = peakstry[0] + try_index[0][0]
                    x0 = self.filtered_x[x0_index]
                    self.peaks[i].append(x0)
                    self.powers[i].append(self.filtered_y[x0_index])
                    self.peaks_index[i].append(x0_index)
                    approximate_fsr = abs(x0 - formerx0)
                    order += 1
                    self.orders[i].append(order)
                    certain_peaks.append(x0_index)
                    x0 += approximate_fsr
                    coeffs = np.polyfit(self.orders[i], self.peaks[i], 1)
                    # coeffs[0] 是斜率 m，coeffs[1] 是截距 b
                    m, b = coeffs
                    self.fsrs[i] = m
                    approximate_fsr = self.fsrs[i]
            x0 = self.peaks[i][0] - approximate_fsr
            order = 0
            while x0 - peakslot / 2 > self.filtered_x[0]:
                approximate_fsr = self.fsrs[i]
                try_index = np.where((self.filtered_x > x0 - peakslot / 2) & (self.filtered_x < x0 + peakslot / 2))
                try_end = try_index[-1][0]
                tryslot_x = self.filtered_x[try_index]
                tryslot_y = self.filtered_y[try_index]
                if np.max(tryslot_y) - np.min(tryslot_y) > 0.01:
                    try_limit = np.min(tryslot_y)
                else:
                    try_limit = -1
                peakstry, _ = find_peaks(-tryslot_y, height=-try_limit, threshold=0, distance=500, prominence=.005,
                                         width=None, wlen=None, rel_height=0.5, plateau_size=None)
                if not peakstry:
                    order -= 1
                    x0 -= approximate_fsr
                    peakslot = 0.1
                else:
                    formerx0 = float(x0 - approximate_fsr)
                    x0_index = peakstry[0] + try_index[0][0]
                    x0 = self.filtered_x[x0_index]
                    self.peaks[i].append(x0)
                    self.powers[i].append(self.filtered_y[x0_index])
                    self.peaks_index[i].append(x0_index)
                    approximate_fsr = abs(x0 - formerx0)
                    certain_peaks.append(x0_index)
                    order -= 1
                    self.orders[i].append(order)
                    x0 -= approximate_fsr
                    coeffs = np.polyfit(self.orders[i], self.peaks[i], 1)
                    # coeffs[0] 是斜率 m，coeffs[1] 是截距 b
                    m, b = coeffs
                    self.fsrs[i] = m
                    approximate_fsr = self.fsrs[i]
                    peakslot = 0.1
            peaks = self.peaks[i]
            if len(peaks) > 1:
                if self.fsrs[i] > 0:
                    approximate_fsr = self.fsrs[i]
                else:
                    approximate_fsr = min([abs(peaks[i] - peaks[i + 1]) for i in range(len(peaks) - 1)])
                orders = [round((peaks[i] - peaks[0]) / approximate_fsr, 0) for i in range(len(peaks))]
                self.orders[i] = orders
            self.update_peaks_info()
            self.plot_peaks()

    def invert0(self):
        self.plot[0] = not self.plot[0]
        self.plot_peaks()

    def invert1(self):
        self.plot[1] = not self.plot[1]
        self.plot_peaks()

    def invert2(self):
        self.plot[2] = not self.plot[2]
        self.plot_peaks()

    def invert3(self):
        self.plot[3] = not self.plot[3]
        self.plot_peaks()

    def invert4(self):
        self.plot[4] = not self.plot[4]
        self.plot_peaks()

    def renew_for_one(self, i):
        self.renew_para()
        self.moredel = 1
        self.fig.canvas.mpl_connect('button_press_event', lambda event, index=i: self.delete_certain_peak(event, index))

    def delete_certain_peak(self, event, i):
        if self.moredel == 1:
            self.peak_in_x = self.filtered_x[
                (self.filtered_x > event.xdata - self.peakslot / 2) & (
                            self.filtered_x < event.xdata + self.peakslot / 2)]
            for to_delete in self.peaks[i]:
                if self.peak_in_x[0] <= to_delete <= self.peak_in_x[-1]:
                    print(to_delete)
                    index = self.peaks[i].index(to_delete)
                    self.peaks[i].remove(to_delete)
                    self.powers[i].__delitem__(index)
                    self.peaks_index[i].__delitem__(index)
                    self.orders[i].__delitem__(index)
                    if len(self.peaks[i]) <= 1:
                        self.fsrs[i] = 0
                    else:
                        coeffs = np.polyfit(self.orders[i], self.peaks[i], 1)
                        # coeffs[0] 是斜率 m，coeffs[1] 是截距 b
                        m, b = coeffs
                        self.fsrs[i] = m
                    self.update_peaks_info()
                    self.plot_peaks()
        if len(self.peaks[i]) == 1:
            self.orders[i] = [0]
        elif len(self.peaks[i]) < 1:
            self.orders[i] = []
        else:
            peaks = self.peaks[i]
            if len(peaks) > 1:
                if self.fsrs[i] > 0:
                    approximate_fsr = self.fsrs[i]
                else:
                    approximate_fsr = min([abs(peaks[i] - peaks[i + 1]) for i in range(len(peaks) - 1)])
                orders = [round((peaks[i] - peaks[0]) / approximate_fsr, 0) for i in range(len(peaks))]
                self.orders[i] = orders
        self.update_peaks_info()
        self.plot_peaks()
        self.moredel = 0

    def prev_step(self):
        """返回上一步"""
        if self.step > 0:
            self.step -= 1
        self.update_ui()

    def next_step(self):
        """进入下一步"""
        if self.step < 3 and self.step//1==self.step:
            self.step += 1
            if self.step<1:
                self.prev_button["state"]="disabled"
                self.next_button["state"] = "enabled"
            else:
                self.prev_button["state"] = "enabled"
                self.next_button["state"] = "enabled"
        else:
            self.step=3
            self.prev_button["state"] = "enabled"
            self.next_button["state"]="disabled"
        self.update_ui()

    # 启动应用
if __name__ == "__main__":
        root = tk.Tk()
        app = Smart_Q_fit(root)
        root.mainloop()


